// #![deny(missing_docs)]
//! test

use ark_ff::{BigInteger256, PrimeField, Zero as _};

use ark_serialize::CanonicalDeserialize;
use ark_serialize::CanonicalSerialize;
use mpc_core::{
    gadgets::poseidon2::Poseidon2,
    protocols::{
        rep3::{Rep3PrimeFieldShare, Rep3State, network::Rep3NetworkExt},
        rep3_ring::Rep3RingShare,
    },
};
use tracing::instrument;

use crate::base::MapBase;
use crate::{insert::InsertTail, update::UpdateTail};
mod base;
pub(crate) mod cosnark;
mod insert;
mod insert_or_update;
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

#[derive(Default, Debug, Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct ObliviousLayer {
    keys: Vec<Rep3RingShare<u32>>,
    values: Vec<Rep3BigIntShare<ark_bn254::Fr>>,
}

impl ObliviousLayer {
    #[cfg(feature = "local")]
    pub fn new(keys: Vec<Rep3RingShare<u32>>, values: Vec<Rep3BigIntShare<ark_bn254::Fr>>) -> Self {
        Self { keys, values }
    }
}

#[derive(Clone)]
pub struct LinearScanObliviousMap {
    inner: MapBase,
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
            inner: MapBase::new(defaults, default_value),
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
            inner: MapBase::from_shared_values(layers, leaf_count, total_count, defaults, root),
            read_groth16,
            write_groth16,
        }
    }

    #[inline(always)]
    pub const fn depth(&self) -> usize {
        LINEAR_SCAN_TREE_DEPTH
    }

    #[inline(always)]
    pub const fn root(&self) -> ark_bn254::Fr {
        self.inner.root
    }

    #[inline(always)]
    pub const fn total_count(&self) -> usize {
        self.inner.total_count
    }

    #[inline(always)]
    pub const fn leaf_count(&self) -> usize {
        self.inner.leaf_count
    }

    pub fn dump(
        &self,
        writer: impl ark_serialize::Write,
        compress: ark_serialize::Compress,
    ) -> eyre::Result<()> {
        self.inner.serialize_with_mode(writer, compress)?;
        Ok(())
    }

    pub fn from_dump(
        reader: impl ark_serialize::Read,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
        read_groth16: Groth16Material,
        write_groth16: Groth16Material,
    ) -> eyre::Result<Self> {
        let inner = MapBase::deserialize_with_mode(reader, compress, validate)?;
        Ok(Self {
            inner,
            read_groth16,
            write_groth16,
        })
    }

    /// Reads the leaf value associated with the provided secret-shared key from the oblivious Merkle tree.
    ///
    /// Read operations can be processed in parallel, but must not overlap with insert or update operations.
    /// Computes a co-SNARK proof for the read, returning the leaf value, proof, and relevant public inputs.
    ///
    /// Needs two network streams that are disjunct from each other for internal parallelizing.
    ///
    /// # Returns
    /// An [`ObliviousReadResult`] containing:
    /// - The secret-shared leaf value
    /// - A co-SNARK proof attesting to the read
    /// - The Merkle root and key commitment as public inputs
    ///
    /// # Errors
    /// Returns an error only if a network failure occurs during the read protocol.
    #[instrument(level = "debug", skip_all)]
    pub fn oblivious_read<N: Rep3NetworkExt>(
        &self,
        req: ObliviousReadRequest,
        net0: &N,
        net1: &N,
        state0: &mut Rep3State,
    ) -> eyre::Result<ObliviousReadResult> {
        let trace = self.inner.read(req, net0, net1, state0)?;
        tracing::debug!("creating co-SNARK");
        self.groth16_read_proof(net0, net1, trace, state0)
    }

    #[instrument(level = "debug", skip_all)]
    pub fn oblivious_insert<N: Rep3NetworkExt>(
        &mut self,
        request: ObliviousInsertRequest,
        net0: &N,
        net1: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<ObliviousWriteResult> {
        tracing::debug!("starting insert! Locking the tree!");
        let insert_with_trace = self.inner.insert(request, net0, net1, state)?;
        let result = self.groth16_insert_proof(net0, net1, insert_with_trace, state);
        tracing::debug!("insert successful!");
        result
    }

    #[instrument(level = "debug", skip_all)]
    pub fn oblivious_update<N: Rep3NetworkExt>(
        &mut self,
        update_request: ObliviousUpdateRequest,
        net0: &N,
        net1: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<ObliviousWriteResult> {
        tracing::debug!("starting update! Locking the tree!");
        let update_with_trace = self.inner.update(update_request, net0, net1, state)?;
        let result = self.groth16_insert_proof(net0, net1, update_with_trace, state);
        tracing::debug!("update successful!");
        result
    }

    pub fn delete<N: Rep3NetworkExt>(
        &mut self,
        key: Rep3RingShare<u32>,
        net0: &N,
        net1: &N,
        randomness_index: Rep3PrimeFieldShare<ark_bn254::Fr>,
        randomness_commitment: Rep3PrimeFieldShare<ark_bn254::Fr>,
        state: &mut Rep3State,
    ) -> eyre::Result<ObliviousWriteResult> {
        // The value in update is only ever used in cmux calls with a secret share, so we can not get any performance advantage by knowing this value in plain. Thus we just use the update protocol.
        //
        // For now we use the default value as deleted marker with focus on the bit-service. There may be use-cases where this is not desired though - in that case we need to change this.
        let default_trivial_share = self.inner.promote_default_value(net0);
        let update_request = ObliviousUpdateRequest {
            key,
            update_value: default_trivial_share,
            randomness_index,
            randomness_commitment,
        };
        self.oblivious_update(update_request, net0, net1, state)
    }

    pub fn oblivious_insert_or_update<N: Rep3NetworkExt>(
        &mut self,
        update_request: ObliviousUpdateRequest,
        net0: &N,
        net1: &N,
        state0: &mut Rep3State,
    ) -> eyre::Result<ObliviousWriteResult> {
        let insert_with_trace = self
            .inner
            .insert_or_update(update_request, net0, net1, state0)?;
        self.groth16_insert_proof(net0, net1, insert_with_trace, state0)
    }

    pub fn prune<N: Rep3NetworkExt>(&mut self, net: &N) -> eyre::Result<()> {
        self.inner.prune(net)
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
        let is_root = LinearScanObliviousMap::new(read_groth16, write_groth16).root();
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
