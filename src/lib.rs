// #![deny(missing_docs)]
//! test
use ark_ff::{BigInteger256, One as _, PrimeField, Zero as _};

use co_noir::Rep3AcvmType;
use itertools::{Itertools as _, izip};
use mpc_core::{
    MpcState as _,
    gadgets::poseidon2::{Poseidon2, Poseidon2Precomputations},
    protocols::{
        rep3::{
            Rep3BigUintShare, Rep3PrimeFieldShare, Rep3State, conversion, id::PartyID,
            network::Rep3NetworkExt,
        },
        rep3_ring::{
            Rep3RingShare,
            ring::{bit::Bit, ring_impl::RingElement},
        },
    },
};
use tracing::instrument;

use crate::{insert::InsertTail, update::UpdateTail};
pub(crate) mod cosnark;
mod insert;
#[cfg(feature = "local")]
pub mod local;
mod mpc;
mod prune;
mod read;
mod update;

pub use cosnark::Groth16Material;
pub use insert::ObliviousInsertRequest;
pub use insert::ObliviousWriteResult;
pub use read::ObliviousReadRequest;
pub use read::ObliviousReadResult;
pub use update::ObliviousUpdateRequest;

pub use mpc::Rep3BigIntShare;

/// The depth of the oblivious-linear-scan-tree.
pub const LINEAR_SCAN_TREE_DEPTH: usize = 32;
const INSERT_PROOF_INPUTS: usize = 68;
const READ_PROOF_INPUTS: usize = 65;

#[derive(Default, Debug, Clone)]
pub struct ObliviousLayer {
    keys: Vec<Rep3RingShare<u32>>,
    values: Vec<Rep3BigIntShare<ark_bn254::Fr>>,
}

struct PoseidonHashesWithTrace {
    new_root: Rep3PrimeFieldShare<ark_bn254::Fr>,
    layer_values: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
    proof_inputs: Vec<Rep3AcvmType<ark_bn254::Fr>>,
    traces: Vec<Vec<Rep3AcvmType<ark_bn254::Fr>>>,
}

struct PoseidonHashesWithTraceInput {
    new_value: Rep3PrimeFieldShare<ark_bn254::Fr>,
    old_value: Rep3PrimeFieldShare<ark_bn254::Fr>,
    bitinject: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
    merkle_witness: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
    randomness_index: Rep3PrimeFieldShare<ark_bn254::Fr>,
    randomness_commitment: Rep3PrimeFieldShare<ark_bn254::Fr>,
    precompute: Poseidon2Precomputations<Rep3PrimeFieldShare<ark_bn254::Fr>>,
}

struct PathAndWitness {
    path: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
    witness: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
}
impl ObliviousLayer {
    #[cfg(feature = "local")]
    pub fn new(keys: Vec<Rep3RingShare<u32>>, values: Vec<Rep3BigIntShare<ark_bn254::Fr>>) -> Self {
        Self { keys, values }
    }
}

#[derive(Clone)]
pub struct LinearScanObliviousMap {
    layers: [ObliviousLayer; LINEAR_SCAN_TREE_DEPTH],
    leaf_count: usize,
    total_count: usize,
    defaults: [BigInteger256; LINEAR_SCAN_TREE_DEPTH],
    root: ark_bn254::Fr,
    read_groth16: Groth16Material,
    write_groth16: Groth16Material,
}

impl LinearScanObliviousMap {
    pub fn new(read_groth16: Groth16Material, write_groth16: Groth16Material) -> Self {
        Self::with_default_value(ark_bn254::Fr::zero(), read_groth16, write_groth16)
    }

    pub fn with_default_value(
        mut default_value: ark_bn254::Fr,
        read_groth16: Groth16Material,
        write_groth16: Groth16Material,
    ) -> Self {
        let poseidon2 = Poseidon2::<ark_bn254::Fr, 2, 5>::default();
        let defaults = std::array::from_fn(|_| {
            let prev = default_value.into_bigint();
            default_value += poseidon2.permutation(&[default_value, default_value])[0];
            prev
        });
        Self {
            layers: std::array::from_fn(|_| ObliviousLayer::default()),
            leaf_count: 0,
            total_count: 0,
            defaults,
            root: default_value,
            read_groth16,
            write_groth16,
        }
    }

    #[cfg(feature = "local")]
    pub fn from_shared_values(
        layers: [ObliviousLayer; LINEAR_SCAN_TREE_DEPTH],
        leaf_count: usize,
        total_count: usize,
        defaults: [BigInteger256; LINEAR_SCAN_TREE_DEPTH],
        root: ark_bn254::Fr,
        read_groth16: Groth16Material,
        write_groth16: Groth16Material,
    ) -> Self {
        Self {
            layers,
            leaf_count,
            total_count,
            defaults,
            root,
            read_groth16,
            write_groth16,
        }
    }

    #[inline(always)]
    pub const fn depth(&self) -> usize {
        LINEAR_SCAN_TREE_DEPTH
    }

    pub fn oblivious_insert_or_update<N: Rep3NetworkExt>(
        &mut self,
        update_request: ObliviousUpdateRequest,
        net0: &N,
        net1: &N,
        state0: &mut Rep3State,
    ) -> eyre::Result<ObliviousWriteResult> {
        let ObliviousUpdateRequest {
            key,
            update_value,
            randomness_index,
            randomness_commitment,
        } = update_request;
        // we need to check if the value is present in the leaf layer.
        // we do that by computing the ohv of the path and xor the leaf values.
        let mut state1 = state0.fork(1).expect("cant fail for rep3");

        let ((present_bit, path_ohv), (merkle_witness, bitinject)) = crate::join(
            || self.is_value_in_leaves(key, net0, state0),
            || {
                let merkle_witness = self.read_merkle_witness(key, net1, &mut state1)?;
                let bitinject = Self::key_decompose(key, net1, &mut state1)?;
                Ok((merkle_witness, bitinject))
            },
        )?;
        let insert_with_trace = if present_bit {
            // is present - need to update
            let update_tail = UpdateTail {
                update_value,
                path_ohv,
                merkle_witness,
                bitinject,
                randomness_index,
                randomness_commitment,
            };
            self.update_tail(update_tail, net0, net1, state0, &mut state1)?
        } else {
            // not present - need to insert
            let insert_tail = InsertTail {
                key,
                insert_value: update_value,
                path_ohv: path_ohv[self.layers[0].values.len()..].to_vec(),
                merkle_witness,
                bitinject,
                randomness_index,
                randomness_commitment,
            };
            self.insert_tail(insert_tail, net0, net1, state0)?
        };
        self.groth16_insert_proof(net0, net1, insert_with_trace, state0)
    }

    fn push_new_values(&mut self, values: Vec<Rep3BigUintShare<ark_bn254::Fr>>) {
        for (layer, new_value) in izip!(self.layers.iter_mut(), values) {
            layer.values.push(new_value.try_into().expect("Works"));
        }
    }

    fn is_value_in_leaves<N: Rep3NetworkExt>(
        &self,
        key: Rep3RingShare<u32>,
        net: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<(bool, Vec<Rep3RingShare<Bit>>)> {
        let path_ohv = crate::mpc::is_zero_many(self.find_path(key), net, state)?;
        let present_bit = path_ohv[..self.layers[0].values.len()]
            .iter()
            .fold(Rep3RingShare::zero_share(), |acc, x| acc ^ *x);
        // open the present bit
        let other = net.reshare(present_bit.b)?;
        let present_bit = other + present_bit.a + present_bit.b;
        Ok((present_bit.convert().convert(), path_ohv))
    }

    #[instrument(level = "debug", skip_all)]
    fn key_decompose<N: Rep3NetworkExt>(
        key: Rep3RingShare<u32>,
        net: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>> {
        // we only need the 32 key-bits
        let key_bits = (0..32).map(|shift| (key >> shift).get_bit(0)).collect_vec();
        // also do the bitinject
        crate::mpc::bit_inject_from_bits_to_field_many(&key_bits, net, state)
    }

    fn promote_default_value<N: Rep3NetworkExt>(
        &self,
        net: &N,
    ) -> Rep3PrimeFieldShare<ark_bn254::Fr> {
        let party_id = net.id().try_into().expect("works for rep3 network");

        mpc_core::protocols::rep3::arithmetic::promote_to_trivial_share(
            party_id,
            self.defaults[0].into(),
        )
    }

    fn find_witness(&self, mut needle: Rep3RingShare<u32>) -> Vec<Rep3RingShare<u32>> {
        // To find the witness
        let mut path_ohv = Vec::with_capacity(self.total_count);
        let one = RingElement::one();
        for layer in self.layers.iter() {
            let neighbor_key = needle ^ one;
            for hay in layer.keys.iter() {
                path_ohv.push(hay ^ &neighbor_key);
            }

            needle.a >>= 1;
            needle.b >>= 1;
        }
        path_ohv
    }

    fn find_path(&self, mut needle: Rep3RingShare<u32>) -> Vec<Rep3RingShare<u32>> {
        // To find the path
        let mut result = Vec::with_capacity(self.total_count);
        for layer in self.layers.iter() {
            for hay in layer.keys.iter() {
                result.push(hay ^ &needle);
            }
            needle.a >>= 1;
            needle.b >>= 1;
        }
        result
    }

    fn read_merkle_path<N: Rep3NetworkExt>(
        &self,
        key: Rep3RingShare<u32>,
        net: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>> {
        let path_ohv = crate::mpc::is_zero_many(self.find_path(key), net, state)?;
        self.read_from_layers_with_ohv(&path_ohv, net, state)
    }

    fn read_merkle_witness<N: Rep3NetworkExt>(
        &self,
        key: Rep3RingShare<u32>,
        net: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>> {
        let path_ohv = crate::mpc::is_zero_many(self.find_witness(key), net, state)?;
        self.read_from_layers_with_ohv(&path_ohv, net, state)
    }

    #[instrument(level = "debug", skip_all)]
    fn read_path_and_witness<N: Rep3NetworkExt>(
        &self,
        key: Rep3RingShare<u32>,
        net0: &N,
        net1: &N,
        state0: &mut Rep3State,
        state1: &mut Rep3State,
    ) -> eyre::Result<PathAndWitness> {
        tracing::trace!("> reading path and witness...");
        let (path, witness) = crate::join(
            || self.read_merkle_path(key, net0, state0),
            || self.read_merkle_witness(key, net1, state1),
        )?;
        tracing::trace!("< reading path and witness...");
        Ok(PathAndWitness { path, witness })
    }

    fn read_from_layers_with_ohv<N: Rep3NetworkExt>(
        &self,
        ohv: &[Rep3RingShare<Bit>],
        net: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>> {
        let mut dots_a = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        let mut start = 0;
        for (layer, default) in izip!(self.layers.iter(), self.defaults.into_iter()) {
            let end = start + layer.keys.len();
            let dot = Self::dot(&ohv[start..end], &layer.values, default, state);
            start = end;
            dots_a.push(dot);
        }
        let dots_b = net.reshare_many(&dots_a)?;
        let dots = izip!(dots_a, dots_b)
            .map(|(a, b)| Rep3BigUintShare::<ark_bn254::Fr>::new(a.into(), b.into()))
            .collect_vec();

        conversion::b2a_many(&dots, net, state)
    }

    fn read_from_leaf_layer<N: Rep3NetworkExt>(
        &self,
        ohv: &[Rep3RingShare<Bit>],
        net: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<Rep3PrimeFieldShare<ark_bn254::Fr>> {
        let leaf_layer = &self.layers[0];

        let dot_a = Self::dot(
            &ohv[..leaf_layer.keys.len()],
            &leaf_layer.values,
            self.defaults[0],
            state,
        );
        let dot_b = net.reshare(dot_a)?;
        let dot = Rep3BigUintShare::<ark_bn254::Fr>::new(dot_a.into(), dot_b.into());

        conversion::b2a(&dot, net, state)
    }
    fn dot(
        ohv: &[Rep3RingShare<Bit>],
        other: &[Rep3BigIntShare<ark_bn254::Fr>],
        default: BigInteger256,
        state: &mut Rep3State,
    ) -> BigInteger256 {
        debug_assert_eq!(
            ohv.len(),
            other.len(),
            "The length of the two vectors must be equal"
        );

        // Set the default value:
        // Assuming only one element was a match, we can dot-product the default value with the injected values as well and calculate: other_value + default_value - sum injected_i * default_value.
        let mut offset = state.id == PartyID::ID0;
        // Start the dot product with a random mask (for potential re-sharing later)
        let (mut dot, dot_b) = state
            .rngs
            .rand
            .random_biguint(ark_bn254::Fr::MODULUS_BIT_SIZE as usize);
        dot ^= dot_b;
        let mut dot = BigInteger256::try_from(dot).expect("Works");
        for (ohv_, other_) in ohv.iter().zip(other.iter()) {
            // This is the AND-gate protocol and we accumulate the results in dot
            if ohv_.a.0.convert() {
                offset ^= true;
                dot ^= other_.a ^ other_.b;
            }
            if ohv_.b.0.convert() {
                dot ^= &other_.a;
            }
        }
        if offset {
            dot ^= default;
        }
        dot
    }
}

fn join<F0, T0, F1, T1>(f0: F0, f1: F1) -> eyre::Result<(T0, T1)>
where
    F0: FnOnce() -> eyre::Result<T0> + Send,
    T0: Send,
    F1: FnOnce() -> eyre::Result<T1> + Send,
    T1: Send,
{
    std::thread::scope(|s| {
        let s0 = s.spawn(f1);
        eyre::Ok((f0()?, s0.join().expect("can join")?))
    })
}

#[cfg(test)]
mod tests {
    use co_noir_to_r1cs::noir::{r1cs, ultrahonk};
    use itertools::izip;
    use mpc_core::protocols::{
        rep3::{self, Rep3State, conversion::A2BType},
        rep3_ring::{self, ring::ring_impl::RingElement},
    };
    use mpc_net::local::LocalNetwork;
    use std::str::FromStr;

    use crate::{
        LinearScanObliviousMap, ObliviousReadRequest, ObliviousUpdateRequest,
        cosnark::Groth16Material,
    };

    const DEFAULT_ROOT_BN254_FR: &str =
        "20656661903863297823367476705363945647184478890034741500819882513030138045548";

    pub fn groth16_material() -> eyre::Result<(Groth16Material, Groth16Material)> {
        let root = std::env!("CARGO_MANIFEST_DIR");
        let read_program = ultrahonk::get_program_artifact(format!(
            "{root}/noir/compiled_circuits/oblivious_map_read.json"
        ))?;
        let write_program = ultrahonk::get_program_artifact(format!(
            "{root}/noir/compiled_circuits/oblivious_map_write.json"
        ))?;
        let (proof_schema_read, pk_read, cs_read) =
            r1cs::setup_r1cs(read_program, &mut rand::thread_rng())?;
        let (proof_schema_write, pk_write, cs_write) =
            r1cs::setup_r1cs(write_program, &mut rand::thread_rng())?;
        Ok((
            Groth16Material::new(proof_schema_read, cs_read, pk_read),
            Groth16Material::new(proof_schema_write, cs_write, pk_write),
        ))
    }

    #[test]
    fn defaults_correct() -> eyre::Result<()> {
        let (read_groth16, write_groth16) = groth16_material()?;
        let is_root = LinearScanObliviousMap::new(read_groth16, write_groth16).root;
        let should_root = ark_bn254::Fr::from_str(DEFAULT_ROOT_BN254_FR).expect("works");
        assert_eq!(is_root, should_root);
        Ok(())
    }

    #[test]
    fn test_oblivious_insert_update() -> eyre::Result<()> {
        const TEST_SUITE: usize = 10;
        let mut rng = rand::thread_rng();

        // generate a random key/values
        let mut keys = Vec::with_capacity(TEST_SUITE);
        let mut values = Vec::with_capacity(TEST_SUITE);
        let mut updates = Vec::with_capacity(TEST_SUITE);
        let mut rands = Vec::with_capacity(TEST_SUITE);
        for _ in 0..TEST_SUITE {
            let mut key = rand::random::<RingElement<u32>>();
            while keys.contains(&key) {
                key = rand::random::<RingElement<u32>>();
            }
            keys.push(key);
            values.push(ark_bn254::Fr::from(rand::random::<u128>()));
            updates.push(ark_bn254::Fr::from(rand::random::<u128>()));
            rands.push(ark_bn254::Fr::from(rand::random::<u128>()));
        }

        let [key_share0, key_share1, key_share2] =
            rep3_ring::share_ring_elements_binary(&keys, &mut rng);
        let [value_share0, value_share1, value_share2] =
            rep3::share_field_elements(&values, &mut rng);
        let [update_share0, update_share1, update_share2] =
            rep3::share_field_elements(&updates, &mut rng);
        let [rand_share0, rand_share1, rand_share2] = rep3::share_field_elements(&rands, &mut rng);
        // need two networks
        let [n0, n1, n2] = LocalNetwork::new_3_parties();
        let [n3, n4, n5] = LocalNetwork::new_3_parties();
        let random_default_value = ark_bn254::Fr::from(rand::random::<u128>());
        let material0 = groth16_material()?;
        let material1 = material0.clone();
        let material2 = material0.clone();
        let read_vk = material0.0.pk.vk.clone();
        let write_vk = material0.1.pk.vk.clone();

        let [res0, res1, res2] = std::thread::scope(|s| {
            let res0 = s.spawn(|| {
                let (read_groth16, write_groth16) = material0;
                let mut map = LinearScanObliviousMap::with_default_value(
                    random_default_value,
                    read_groth16,
                    write_groth16,
                );
                let mut state = Rep3State::new(&n0, A2BType::Direct).expect("works");
                let mut inserts = Vec::with_capacity(TEST_SUITE);
                let mut read_after_insert = Vec::with_capacity(TEST_SUITE);
                let mut updates = Vec::with_capacity(TEST_SUITE);
                let mut read_after_update = Vec::with_capacity(TEST_SUITE);

                for (key, insert_value, update_value, r) in
                    izip!(key_share0, value_share0, update_share0, rand_share0)
                {
                    let read_request = ObliviousReadRequest {
                        key,
                        randomness_commitment: r,
                    };
                    let insert_req = ObliviousUpdateRequest {
                        key,
                        update_value: insert_value,
                        randomness_index: r,
                        randomness_commitment: r,
                    };
                    let update_req = ObliviousUpdateRequest {
                        key,
                        update_value,
                        randomness_index: r,
                        randomness_commitment: r,
                    };
                    inserts.push(map.oblivious_insert_or_update(insert_req, &n0, &n3, &mut state)?);
                    read_after_insert.push(map.oblivious_read(
                        read_request,
                        &n0,
                        &n3,
                        &mut state,
                    )?);
                    updates.push(map.oblivious_insert_or_update(update_req, &n0, &n3, &mut state)?);
                    read_after_update.push(map.oblivious_read(
                        read_request,
                        &n0,
                        &n3,
                        &mut state,
                    )?);
                }
                eyre::Ok((inserts, read_after_insert, updates, read_after_update))
            });

            let res1 = s.spawn(|| {
                let (read_groth16, write_groth16) = material1;
                let mut map = LinearScanObliviousMap::with_default_value(
                    random_default_value,
                    read_groth16,
                    write_groth16,
                );
                let mut state = Rep3State::new(&n1, A2BType::Direct).expect("works");
                let mut inserts = Vec::with_capacity(TEST_SUITE);
                let mut read_after_insert = Vec::with_capacity(TEST_SUITE);
                let mut updates = Vec::with_capacity(TEST_SUITE);
                let mut reads_updates = Vec::with_capacity(TEST_SUITE);

                for (key, insert_value, update_value, r) in
                    izip!(key_share1, value_share1, update_share1, rand_share1)
                {
                    let read_request = ObliviousReadRequest {
                        key,
                        randomness_commitment: r,
                    };
                    let insert_req = ObliviousUpdateRequest {
                        key,
                        update_value: insert_value,
                        randomness_index: r,
                        randomness_commitment: r,
                    };
                    let update_req = ObliviousUpdateRequest {
                        key,
                        update_value,
                        randomness_index: r,
                        randomness_commitment: r,
                    };
                    inserts.push(map.oblivious_insert_or_update(insert_req, &n1, &n4, &mut state)?);
                    read_after_insert.push(map.oblivious_read(
                        read_request,
                        &n1,
                        &n4,
                        &mut state,
                    )?);
                    updates.push(map.oblivious_insert_or_update(update_req, &n1, &n4, &mut state)?);
                    reads_updates.push(map.oblivious_read(read_request, &n1, &n4, &mut state)?);
                }
                eyre::Ok((inserts, read_after_insert, updates, reads_updates))
            });

            let res2 = s.spawn(|| {
                let (read_groth16, write_groth16) = material2;
                let mut map = LinearScanObliviousMap::with_default_value(
                    random_default_value,
                    read_groth16,
                    write_groth16,
                );
                let mut state = Rep3State::new(&n2, A2BType::Direct).expect("works");
                let mut inserts = Vec::with_capacity(TEST_SUITE);
                let mut read_after_insert = Vec::with_capacity(TEST_SUITE);
                let mut updates = Vec::with_capacity(TEST_SUITE);
                let mut reads_updates = Vec::with_capacity(TEST_SUITE);

                for (key, insert_value, update_value, r) in
                    izip!(key_share2, value_share2, update_share2, rand_share2)
                {
                    let read_request = ObliviousReadRequest {
                        key,
                        randomness_commitment: r,
                    };

                    let insert_req = ObliviousUpdateRequest {
                        key,
                        update_value: insert_value,
                        randomness_index: r,
                        randomness_commitment: r,
                    };
                    let update_req = ObliviousUpdateRequest {
                        key,
                        update_value,
                        randomness_index: r,
                        randomness_commitment: r,
                    };
                    inserts.push(map.oblivious_insert_or_update(insert_req, &n2, &n5, &mut state)?);
                    read_after_insert.push(map.oblivious_read(
                        read_request,
                        &n2,
                        &n5,
                        &mut state,
                    )?);
                    updates.push(map.oblivious_insert_or_update(update_req, &n2, &n5, &mut state)?);
                    reads_updates.push(map.oblivious_read(read_request, &n2, &n5, &mut state)?);
                }
                eyre::Ok((inserts, read_after_insert, updates, reads_updates))
            });
            let res0 = res0.join().expect("can join").expect("did work");
            let res1 = res1.join().expect("can join").expect("did work");
            let res2 = res2.join().expect("can join").expect("did work");
            [res0, res1, res2]
        });

        let (inserts0, read_after_insert0, updates0, read_after_update0) = res0;
        let (inserts1, read_after_insert1, updates1, read_after_update1) = res1;
        let (inserts2, read_after_insert2, updates2, read_after_update2) = res2;

        for (i0, i1, i2) in izip!(inserts0, inserts1, inserts2) {
            assert_eq!(i0.new_root, i1.new_root);
            assert_eq!(i1.new_root, i2.new_root);

            assert!(r1cs::verify(&write_vk, &i0.proof, &i0.inputs_to_vec())?);
            assert!(r1cs::verify(&write_vk, &i1.proof, &i1.inputs_to_vec())?);
            assert!(r1cs::verify(&write_vk, &i2.proof, &i2.inputs_to_vec())?);
        }

        for (r0, r1, r2, should_read) in izip!(
            read_after_insert0,
            read_after_insert1,
            read_after_insert2,
            values
        ) {
            let is_read = r0.read.a + r1.read.a + r2.read.a;
            assert_eq!(is_read, should_read);

            assert!(r1cs::verify(
                &read_vk,
                &r0.proof,
                &[r0.root, r0.commitment]
            )?);
            assert!(r1cs::verify(
                &read_vk,
                &r1.proof,
                &[r1.root, r1.commitment]
            )?);
            assert!(r1cs::verify(
                &read_vk,
                &r2.proof,
                &[r2.root, r2.commitment]
            )?);
        }

        for (u0, u1, u2) in izip!(updates0, updates1, updates2) {
            assert_eq!(u0.new_root, u1.new_root);
            assert_eq!(u1.new_root, u2.new_root);

            assert!(r1cs::verify(&write_vk, &u0.proof, &u0.inputs_to_vec())?);
            assert!(r1cs::verify(&write_vk, &u1.proof, &u1.inputs_to_vec())?);
            assert!(r1cs::verify(&write_vk, &u2.proof, &u2.inputs_to_vec())?);
        }

        for (r0, r1, r2, should_read) in izip!(
            read_after_update0,
            read_after_update1,
            read_after_update2,
            updates
        ) {
            let is_read = r0.read.a + r1.read.a + r2.read.a;
            assert_eq!(is_read, should_read);

            assert!(r1cs::verify(
                &read_vk,
                &r0.proof,
                &[r0.root, r0.commitment]
            )?);
            assert!(r1cs::verify(
                &read_vk,
                &r1.proof,
                &[r1.root, r1.commitment]
            )?);
            assert!(r1cs::verify(
                &read_vk,
                &r2.proof,
                &[r2.root, r2.commitment]
            )?);
        }

        Ok(())
    }
}
