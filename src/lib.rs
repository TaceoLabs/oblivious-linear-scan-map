use ark_ff::{BigInteger256, One as _, PrimeField, Zero as _};

use itertools::{Itertools as _, izip};
use mpc_core::{
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
use mpc_net::Network;

use crate::rep3::Rep3BigIntShare;
mod groth16;
mod insert;
#[cfg(feature = "local")]
pub mod local;
pub mod read;
pub mod rep3;
//mod update;

pub use groth16::Groth16Material;

pub const DELETED_LEAF_VALUE: u64 = 0xDEADBEEF;
pub const LINEAR_SCAN_TREE_DEPTH: usize = 32;

#[derive(Clone)]
/// A witness of proving one layer in a Merkle tree.
struct ObliviousMerkleWitnessElement {
    /// Determines the other value required to compute the hash for the next layer.
    pub other: Rep3PrimeFieldShare<ark_bn254::Fr>,
    /// Determines the position for the prove element in the hash for current layer.
    pub position: Rep3PrimeFieldShare<ark_bn254::Fr>, // Index of the prove element
}

#[derive(Default, Debug, Clone)]
pub struct ObliviousLayer {
    keys: Vec<Rep3RingShare<u32>>,
    values: Vec<Rep3BigIntShare<ark_bn254::Fr>>,
}

impl ObliviousLayer {
    pub fn new(keys: Vec<Rep3RingShare<u32>>, values: Vec<Rep3BigIntShare<ark_bn254::Fr>>) -> Self {
        Self { keys, values }
    }
}

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

    // finds the path of the member (its neighbors)
    fn find_path_and_key_decompose(
        &self,
        mut needle: Rep3RingShare<u32>,
    ) -> (Vec<Rep3RingShare<Bit>>, Vec<Rep3RingShare<u32>>) {
        // To find the path
        let mut to_compare = Vec::with_capacity(self.total_count);
        let mut key_bits = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        let one = RingElement::one();
        for layer in self.layers.iter() {
            let neighbor_key = needle ^ one;
            for hay in layer.keys.iter() {
                to_compare.push(hay ^ &neighbor_key);
            }
            let lsb = needle.get_bit(0);
            key_bits.push(lsb);

            needle.a >>= 1;
            needle.b >>= 1;
        }
        (key_bits, to_compare)
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
        // Start the dot product with a random mask (for potential resharing later)
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

    fn compute_merkle_path<N: Network>(
        &self,
        ohv: &[Rep3RingShare<Bit>],
        bitinject: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
        net: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<Vec<ObliviousMerkleWitnessElement>> {
        let mut dots_a = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        let mut start = 0;
        for (layer, default) in izip!(self.layers.iter(), self.defaults) {
            let end = start + layer.keys.len();
            let dot = Self::dot(&ohv[start..end], &layer.values, default, state);
            start = end;

            dots_a.push(dot);
        }
        let dots_b = net.reshare_many(&dots_a)?;

        let dots = izip!(dots_a, dots_b)
            .map(|(a, b)| Rep3BigUintShare::new(a.into(), b.into()))
            .collect_vec();

        let dots = conversion::b2a_many(&dots, net, state)?;

        let path = izip!(dots, bitinject)
            .map(|(other, position)| ObliviousMerkleWitnessElement { other, position })
            .collect_vec();
        Ok(path)
    }

    fn poseidon2_cmux<N: Network>(
        p: &ObliviousMerkleWitnessElement,
        element: Rep3PrimeFieldShare<ark_bn254::Fr>,
        net: &N,
        poseidon2: &Poseidon2<ark_bn254::Fr, 2, 5>,
        poseidon2_precomputations: &mut Poseidon2Precomputations<
            Rep3PrimeFieldShare<ark_bn254::Fr>,
        >,
    ) -> eyre::Result<Rep3PrimeFieldShare<ark_bn254::Fr>> {
        // left = if p.position == 0 value else other_value
        // right = if p.position == 0 other_value else value
        let left_a = (p.other - element) * p.position + element.a;
        let right_a = (element - p.other) * p.position + p.other.a;
        let bs = net.reshare_many(&[left_a, right_a])?;
        let left = Rep3PrimeFieldShare::new(left_a, bs[0]);
        let right = Rep3PrimeFieldShare::new(right_a, bs[1]);
        let mut poseidon_inputs = [left, right];
        poseidon2.rep3_permutation_in_place_with_precomputation(
            &mut poseidon_inputs,
            poseidon2_precomputations,
            net,
        )?;
        Ok(poseidon_inputs[0] + left)
    }
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

    use crate::{LinearScanObliviousMap, groth16::Groth16Material};

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
    fn read_empty_map() -> eyre::Result<()> {
        let mut rng = rand::thread_rng();

        // generate a random key
        let key = RingElement(rand::random::<u32>());
        let randomness_commitment = ark_bn254::Fr::from(rand::random::<u128>());

        let [key_share0, key_share1, key_share2] =
            rep3_ring::share_ring_element_binary(key, &mut rng);

        let [r0, r1, r2] = rep3::share_field_element(randomness_commitment, &mut rng);

        // need two networks
        let [n0, n1, n2] = LocalNetwork::new_3_parties();
        let [n3, n4, n5] = LocalNetwork::new_3_parties();
        let random_default_value = ark_bn254::Fr::from(rand::random::<u128>());

        let material0 = groth16_material()?;
        let material1 = groth16_material()?;
        let material2 = groth16_material()?;
        let read_vk = material0.0.pk.vk.clone();

        let [res0, res1, res2] = std::thread::scope(|s| {
            let res0 = s.spawn(|| {
                let (read_groth16, write_groth16) = material0;
                let map = LinearScanObliviousMap::with_default_value(
                    random_default_value,
                    read_groth16,
                    write_groth16,
                );
                let mut state = Rep3State::new(&n0, A2BType::Direct).expect("works");
                let read_value = map.oblivious_read(key_share0, &n0, &n3, r0, &mut state)?;
                eyre::Ok(read_value)
            });

            let res1 = s.spawn(|| {
                let (read_groth16, write_groth16) = material1;
                let map = LinearScanObliviousMap::with_default_value(
                    random_default_value,
                    read_groth16,
                    write_groth16,
                );
                let mut state = Rep3State::new(&n1, A2BType::Direct).expect("works");
                map.oblivious_read(key_share1, &n1, &n4, r1, &mut state)
            });

            let res2 = s.spawn(|| {
                let (read_groth16, write_groth16) = material2;
                let map = LinearScanObliviousMap::with_default_value(
                    random_default_value,
                    read_groth16,
                    write_groth16,
                );
                let mut state = Rep3State::new(&n2, A2BType::Direct).expect("works");
                map.oblivious_read(key_share2, &n2, &n5, r2, &mut state)
            });
            let res0 = res0.join().expect("can join").expect("did work");
            let res1 = res1.join().expect("can join").expect("did work");
            let res2 = res2.join().expect("can join").expect("did work");
            [res0, res1, res2]
        });

        let read_value = (res0.read + res1.read + res2.read).a;
        assert_eq!(read_value, random_default_value);

        // verify the proofs
        assert!(r1cs::verify(&read_vk, &res0.proof, &res0.public_inputs)?);
        assert!(r1cs::verify(&read_vk, &res1.proof, &res1.public_inputs)?);
        assert!(r1cs::verify(&read_vk, &res2.proof, &res2.public_inputs)?);

        Ok(())
    }

    #[test]
    fn insert_then_read() -> eyre::Result<()> {
        const TEST_SUITE: usize = 1;
        let mut rng = rand::thread_rng();

        // generate a random key/values
        let mut keys = Vec::with_capacity(TEST_SUITE);
        let mut values = Vec::with_capacity(TEST_SUITE);
        let mut rands = Vec::with_capacity(TEST_SUITE);
        for _ in 0..TEST_SUITE {
            let mut key = rand::random::<RingElement<u32>>();
            while keys.contains(&key) {
                key = rand::random::<RingElement<u32>>();
            }
            keys.push(key);
            values.push(ark_bn254::Fr::from(rand::random::<u128>()));
            rands.push(ark_bn254::Fr::from(rand::random::<u128>()));
        }

        let [key_share0, key_share1, key_share2] =
            rep3_ring::share_ring_elements_binary(&keys, &mut rng);
        let [value_share0, value_share1, value_share2] =
            rep3::share_field_elements(&values, &mut rng);
        let [rand_share0, rand_share1, rand_share2] = rep3::share_field_elements(&rands, &mut rng);

        // need two networks
        let [n0, n1, n2] = LocalNetwork::new_3_parties();
        let [n3, n4, n5] = LocalNetwork::new_3_parties();
        let random_default_value = ark_bn254::Fr::from(rand::random::<u128>());

        let material0 = groth16_material()?;
        let material1 = groth16_material()?;
        let material2 = groth16_material()?;
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
                let mut reads = Vec::with_capacity(TEST_SUITE);
                let mut inserts = Vec::with_capacity(TEST_SUITE);
                let mut defaults = Vec::with_capacity(TEST_SUITE);

                for (k, v, r) in izip!(key_share0, value_share0, rand_share0) {
                    // read first on key before insert
                    defaults.push(map.oblivious_read(k, &n0, &n3, r, &mut state)?);
                    inserts.push(map.oblivious_insert(k, v, &n0, &n3, r, r, &mut state)?);
                    reads.push(map.oblivious_read(k, &n0, &n3, r, &mut state)?);
                }
                eyre::Ok((reads, inserts, defaults))
            });

            let res1 = s.spawn(|| {
                let (read_groth16, write_groth16) = material1;
                let mut map = LinearScanObliviousMap::with_default_value(
                    random_default_value,
                    read_groth16,
                    write_groth16,
                );
                let mut state = Rep3State::new(&n1, A2BType::Direct).expect("works");
                let mut reads = Vec::with_capacity(TEST_SUITE);
                let mut inserts = Vec::with_capacity(TEST_SUITE);
                let mut defaults = Vec::with_capacity(TEST_SUITE);

                for (k, v, r) in izip!(key_share1, value_share1, rand_share1) {
                    // read first on key before insert
                    defaults.push(map.oblivious_read(k, &n1, &n4, r, &mut state)?);
                    inserts.push(map.oblivious_insert(k, v, &n1, &n4, r, r, &mut state)?);
                    reads.push(map.oblivious_read(k, &n1, &n4, r, &mut state)?);
                }
                eyre::Ok((reads, inserts, defaults))
            });

            let res2 = s.spawn(|| {
                let (read_groth16, write_groth16) = material2;
                let mut map = LinearScanObliviousMap::with_default_value(
                    random_default_value,
                    read_groth16,
                    write_groth16,
                );
                let mut state = Rep3State::new(&n2, A2BType::Direct).expect("works");
                let mut reads = Vec::with_capacity(TEST_SUITE);
                let mut inserts = Vec::with_capacity(TEST_SUITE);
                let mut defaults = Vec::with_capacity(TEST_SUITE);

                for (k, v, r) in izip!(key_share2, value_share2, rand_share2) {
                    // read first on key before insert
                    defaults.push(map.oblivious_read(k, &n2, &n5, r, &mut state)?);
                    inserts.push(map.oblivious_insert(k, v, &n2, &n5, r, r, &mut state)?);
                    reads.push(map.oblivious_read(k, &n2, &n5, r, &mut state)?);
                }
                eyre::Ok((reads, inserts, defaults))
            });
            let res0 = res0.join().expect("can join").expect("did work");
            let res1 = res1.join().expect("can join").expect("did work");
            let res2 = res2.join().expect("can join").expect("did work");
            [res0, res1, res2]
        });

        let (reads0, inserts0, defaults0) = res0;
        let (reads1, inserts1, defaults1) = res1;
        let (reads2, inserts2, defaults2) = res2;

        for (d0, d1, d2) in izip!(defaults0, defaults1, defaults2) {
            let is_default = d0.read.a + d1.read.a + d2.read.a;
            assert_eq!(is_default, random_default_value);

            assert!(r1cs::verify(&read_vk, &d0.proof, &d0.public_inputs)?);
            assert!(r1cs::verify(&read_vk, &d1.proof, &d1.public_inputs)?);
            assert!(r1cs::verify(&read_vk, &d2.proof, &d2.public_inputs)?);
        }

        for (i0, i1, i2) in izip!(inserts0, inserts1, inserts2) {
            assert_eq!(i0.new_root, i1.new_root);
            assert_eq!(i1.new_root, i2.new_root);

            assert!(r1cs::verify(&write_vk, &i0.proof, &i0.public_inputs)?);
            assert!(r1cs::verify(&write_vk, &i1.proof, &i1.public_inputs)?);
            assert!(r1cs::verify(&write_vk, &i2.proof, &i2.public_inputs)?);
        }

        for (r0, r1, r2, should_read) in izip!(reads0, reads1, reads2, values) {
            let is_read = r0.read.a + r1.read.a + r2.read.a;
            assert_eq!(is_read, should_read);

            assert!(r1cs::verify(&read_vk, &r0.proof, &r0.public_inputs)?);
            assert!(r1cs::verify(&read_vk, &r1.proof, &r1.public_inputs)?);
            assert!(r1cs::verify(&read_vk, &r2.proof, &r2.public_inputs)?);
        }
        Ok(())
    }

    // #[test]
    // fn insert_update_then_read() {
    //     const TEST_SUITE: usize = 100;
    //     let mut rng = rand::thread_rng();

    //     // generate a random key/values
    //     let mut keys = Vec::with_capacity(TEST_SUITE);
    //     let mut values = Vec::with_capacity(TEST_SUITE);
    //     let mut updates = Vec::with_capacity(TEST_SUITE);
    //     for _ in 0..TEST_SUITE {
    //         let mut key = rand::random::<RingElement<u32>>();
    //         while keys.contains(&key) {
    //             key = rand::random::<RingElement<u32>>();
    //         }
    //         keys.push(key);
    //         values.push(ark_bn254::Fr::from(rand::random::<u128>()));
    //         updates.push(ark_bn254::Fr::from(rand::random::<u128>()));
    //     }

    //     let [key_share0, key_share1, key_share2] =
    //         rep3_ring::share_ring_elements_binary(&keys, &mut rng);
    //     let [value_share0, value_share1, value_share2] =
    //         rep3::share_field_elements(&values, &mut rng);
    //     let [update_share0, update_share1, update_share2] =
    //         rep3::share_field_elements(&updates, &mut rng);
    //     // need two networks
    //     let [n0, n1, n2] = LocalNetwork::new_3_parties();
    //     let [n3, n4, n5] = LocalNetwork::new_3_parties();
    //     let random_default_value = ark_bn254::Fr::from(rand::random::<u128>());

    //     let [res0, res1, res2] = std::thread::scope(|s| {
    //         let res0 = s.spawn(|| {
    //             let mut map = LinearScanObliviousMap::with_default_value(random_default_value);
    //             let mut state = Rep3State::new(&n0, A2BType::Direct).expect("works");
    //             let mut reads = Vec::with_capacity(TEST_SUITE);
    //             let mut path_checks = Vec::with_capacity(TEST_SUITE * 3);

    //             for (k, v, u) in izip!(key_share0, value_share0, update_share0) {
    //                 // insert
    //                 let insert_path = map.insert(k, v, &n0, &n3, &mut state)?;
    //                 path_checks.push(map.verify_path(v, &insert_path, &n0, &mut state)?);

    //                 // update
    //                 let update_path = map.update(k, u, &n0, &n3, &mut state)?;
    //                 path_checks.push(map.verify_path(u, &update_path, &n0, &mut state)?);

    //                 // verify
    //                 let read_value = map.read_path_and_witness(k, &n0, &n3, &mut state)?.path[0];
    //                 reads.push(read_value);
    //             }
    //             eyre::Ok((reads, path_checks))
    //         });

    //         let res1 = s.spawn(|| {
    //             let mut map = LinearScanObliviousMap::with_default_value(random_default_value);
    //             let mut state = Rep3State::new(&n1, A2BType::Direct).expect("works");
    //             let mut reads = Vec::with_capacity(TEST_SUITE);
    //             let mut path_checks = Vec::with_capacity(TEST_SUITE * 3);

    //             for (k, v, u) in izip!(key_share1, value_share1, update_share1) {
    //                 // insert
    //                 let insert_path = map.insert(k, v, &n1, &n4, &mut state)?;
    //                 path_checks.push(map.verify_path(v, &insert_path, &n1, &mut state)?);

    //                 // update
    //                 let update_path = map.update(k, u, &n1, &n4, &mut state)?;
    //                 path_checks.push(map.verify_path(u, &update_path, &n1, &mut state)?);

    //                 // verify
    //                 let read_value = map.read_path_and_witness(k, &n1, &n4, &mut state)?.path[0];
    //                 reads.push(read_value);
    //             }
    //             eyre::Ok((reads, path_checks))
    //         });

    //         let res2 = s.spawn(|| {
    //             let mut map = LinearScanObliviousMap::with_default_value(random_default_value);
    //             let mut state = Rep3State::new(&n2, A2BType::Direct).expect("works");
    //             let mut reads = Vec::with_capacity(TEST_SUITE);
    //             let mut path_checks = Vec::with_capacity(TEST_SUITE * 3);

    //             for (k, v, u) in izip!(key_share2, value_share2, update_share2) {
    //                 // insert
    //                 let insert_path = map.insert(k, v, &n2, &n5, &mut state)?;
    //                 path_checks.push(map.verify_path(v, &insert_path, &n2, &mut state)?);

    //                 // update
    //                 let update_path = map.update(k, u, &n2, &n5, &mut state)?;
    //                 path_checks.push(map.verify_path(u, &update_path, &n2, &mut state)?);

    //                 // verify
    //                 let read_value = map.read_path_and_witness(k, &n2, &n5, &mut state)?.path[0];
    //                 reads.push(read_value);
    //             }
    //             eyre::Ok((reads, path_checks))
    //         });
    //         let res0 = res0.join().expect("can join").expect("did work");
    //         let res1 = res1.join().expect("can join").expect("did work");
    //         let res2 = res2.join().expect("can join").expect("did work");
    //         [res0, res1, res2]
    //     });

    //     let (reads0, checks0) = res0;
    //     let (reads1, checks1) = res1;
    //     let (reads2, checks2) = res2;

    //     for (r0, r1, r2, should) in izip!(reads0, reads1, reads2, updates) {
    //         assert_eq!((r0 + r1 + r2).a, should);
    //     }

    //     for (r0, r1, r2) in izip!(checks0, checks1, checks2) {
    //         assert!((r0 + r1 + r2).a.convert().convert());
    //     }
    // }

    // #[test]
    // pub fn insert_then_read_proof() {
    //     const TEST_SUITE: usize = 1;
    //     let mut rng = rand::thread_rng();

    //     // generate a random key/values
    //     let mut keys = Vec::with_capacity(TEST_SUITE);
    //     let mut values = Vec::with_capacity(TEST_SUITE);
    //     for _ in 0..TEST_SUITE {
    //         let mut key = rand::random::<RingElement<u32>>();
    //         while keys.contains(&key) {
    //             key = rand::random::<RingElement<u32>>();
    //         }
    //         keys.push(key);
    //         values.push(ark_bn254::Fr::from(rand::random::<u128>()));
    //     }

    //     let [key_share0, key_share1, key_share2] =
    //         rep3_ring::share_ring_elements_binary(&keys, &mut rng);
    //     let [value_share0, value_share1, value_share2] =
    //         rep3::share_field_elements(&values, &mut rng);
    //     // just use the same random value, doesn't really matter
    //     let [r0, r1, r2] = rep3::share_field_element(ark_bn254::Fr::rand(&mut rng), &mut rng);

    //     // need two networks
    //     let [n0, n1, n2] = LocalNetwork::new_3_parties();
    //     let [n3, n4, n5] = LocalNetwork::new_3_parties();
    //     let random_default_value = ark_bn254::Fr::from(rand::random::<u128>());

    //     let root = std::env!("CARGO_MANIFEST_DIR");
    //     let read_program = ultrahonk::get_program_artifact(format!(
    //         "{root}/noir/compiled_circuits/oblivious_map_read.json"
    //     ))
    //     .unwrap();
    //     let (proof_schema, pk, cs) = r1cs::setup_r1cs(read_program, &mut rng).unwrap();
    //     let proof_schema = Arc::new(proof_schema);
    //     let pk = Arc::new(pk);
    //     let cs = Arc::new(cs);

    //     let [res0, res1, res2] = std::thread::scope(|s| {
    //         let res0 = s.spawn(|| {
    //             let mut map = LinearScanObliviousMap::with_default_value(random_default_value);
    //             let mut state = Rep3State::new(&n0, A2BType::Direct).expect("works");
    //             let mut reads = Vec::with_capacity(TEST_SUITE);

    //             for (k, v) in izip!(key_share0, value_share0) {
    //                 // read first on key before insert
    //                 map.insert(k, v, &n0, &n3, &mut state)?;
    //                 reads.push(map.read_e2e(
    //                     k,
    //                     &n0,
    //                     &n3,
    //                     r0,
    //                     &mut state,
    //                     &proof_schema,
    //                     &cs,
    //                     &pk,
    //                 )?);
    //             }
    //             eyre::Ok(reads)
    //         });

    //         let res1 = s.spawn(|| {
    //             let mut map = LinearScanObliviousMap::with_default_value(random_default_value);
    //             let mut state = Rep3State::new(&n1, A2BType::Direct).expect("works");
    //             let mut reads = Vec::with_capacity(TEST_SUITE);

    //             for (k, v) in izip!(key_share1, value_share1) {
    //                 // read first on key before insert
    //                 map.insert(k, v, &n1, &n4, &mut state)?;
    //                 reads.push(map.read_e2e(
    //                     k,
    //                     &n1,
    //                     &n4,
    //                     r1,
    //                     &mut state,
    //                     &proof_schema,
    //                     &cs,
    //                     &pk,
    //                 )?);
    //             }
    //             eyre::Ok(reads)
    //         });

    //         let res2 = s.spawn(|| {
    //             let mut map = LinearScanObliviousMap::with_default_value(random_default_value);
    //             let mut state = Rep3State::new(&n2, A2BType::Direct).expect("works");
    //             let mut reads = Vec::with_capacity(TEST_SUITE);

    //             for (k, v) in izip!(key_share2, value_share2) {
    //                 // read first on key before insert
    //                 map.insert(k, v, &n2, &n5, &mut state)?;
    //                 reads.push(map.read_e2e(
    //                     k,
    //                     &n2,
    //                     &n5,
    //                     r2,
    //                     &mut state,
    //                     &proof_schema,
    //                     &cs,
    //                     &pk,
    //                 )?);
    //             }
    //             eyre::Ok(reads)
    //         });
    //         let res0 = res0.join().expect("can join").expect("did work");
    //         let res1 = res1.join().expect("can join").expect("did work");
    //         let res2 = res2.join().expect("can join").expect("did work");
    //         [res0, res1, res2]
    //     });

    //     for (res0, res1, res2, should) in izip!(res0, res1, res2, values) {
    //         let (reads0, proof0, public_input0) = res0;
    //         let (reads1, proof1, public_input1) = res1;
    //         let (reads2, proof2, public_input2) = res2;
    //         assert!(
    //             r1cs::verify(&pk.vk, &proof0, &public_input0).unwrap(),
    //             "proof verifies"
    //         );
    //         assert!(
    //             r1cs::verify(&pk.vk, &proof1, &public_input1).unwrap(),
    //             "proof verifies"
    //         );
    //         assert!(
    //             r1cs::verify(&pk.vk, &proof2, &public_input2).unwrap(),
    //             "proof verifies"
    //         );
    //         assert_eq!((reads0 + reads1 + reads2).a, should);
    //     }
    // }
}
