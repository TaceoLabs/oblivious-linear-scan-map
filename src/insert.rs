use co_noir::{Bn254, Rep3AcvmType};
use itertools::izip;
use mpc_core::{
    MpcState,
    gadgets::poseidon2::Poseidon2,
    protocols::{
        rep3::{Rep3PrimeFieldShare, Rep3State, arithmetic, conversion, network::Rep3NetworkExt},
        rep3_ring::{Rep3RingShare, ring::bit::Bit},
    },
};
use tracing::instrument;

use crate::{
    INSERT_PROOF_INPUTS, LINEAR_SCAN_TREE_DEPTH, LinearScanObliviousMap,
    base::{MapBase, PoseidonHashesWithTrace, PoseidonHashesWithTraceInput},
    cosnark::{self, InsertWithTrace},
};

/// Request for an insert operation on the oblivious Merkle tree.
///
/// Contains the secret-shared key, the value to insert, and secret-shared randomness used for commitment to the key and the value.
pub struct ObliviousInsertRequest {
    /// Secret-shared key identifying the target leaf.
    pub key: Rep3RingShare<u32>,
    /// Secret-shared value to insert at the key.
    pub insert_value: Rep3PrimeFieldShare<ark_bn254::Fr>,
    /// Secret-shared randomness used for the key commitment.
    pub randomness_index: Rep3PrimeFieldShare<ark_bn254::Fr>,
    /// Secret-shared randomness used for the commitment to the inserted value.
    pub randomness_commitment: Rep3PrimeFieldShare<ark_bn254::Fr>,
}

/// Response to an oblivious insert operation.
///
/// Returns the new Merkle root, a co-SNARK proof for the insert, and public inputs for verification.
pub struct ObliviousWriteResult {
    pub proof: ark_groth16::Proof<Bn254>,
    pub old_root: ark_bn254::Fr,
    pub new_root: ark_bn254::Fr,
    pub commitment_key: ark_bn254::Fr,
    pub commitment_value: ark_bn254::Fr,
}

/// Input to the `insert_tail` function.
///
/// Needed because we either call `insert_tail` from insert or update_or_insert.
pub(super) struct InsertTail {
    pub(super) key: Rep3RingShare<u32>,
    pub(super) insert_value: Rep3PrimeFieldShare<ark_bn254::Fr>,
    pub(super) path_ohv: Vec<Rep3RingShare<Bit>>,
    pub(super) merkle_witness: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
    pub(super) bitinject: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
    pub(super) randomness_index: Rep3PrimeFieldShare<ark_bn254::Fr>,
    pub(super) randomness_commitment: Rep3PrimeFieldShare<ark_bn254::Fr>,
}

impl MapBase {
    #[instrument(level = "debug", skip_all)]
    pub(super) fn insert<N: Rep3NetworkExt>(
        &mut self,
        request: ObliviousInsertRequest,
        net0: &N,
        net1: &N,
        state0: &mut Rep3State,
    ) -> eyre::Result<InsertWithTrace> {
        let ObliviousInsertRequest {
            key,
            insert_value,
            randomness_index,
            randomness_commitment,
        } = request;
        let mut state1 = state0.fork(1).expect("cant fail for rep3");
        let (path_ohv, (merkle_witness, bitinject)) =
            tracing::debug_span!("insert::read_path_and_witness").in_scope(|| {
                tracing::debug!("reading path_ohv, witness and decompose in parallel...");
                crate::join(
                    || {
                        let path_ohv = self.find_path_skip_leaf_layer(key);
                        crate::mpc::is_zero_many(path_ohv, net0, state0)
                    },
                    || {
                        let merkle_witness = self.read_merkle_witness(key, net1, &mut state1)?;
                        let bitinject = Self::key_decompose(key, net1, &mut state1)?;
                        Ok((merkle_witness, bitinject))
                    },
                )
            })?;

        let insert_tail = InsertTail {
            key,
            insert_value,
            path_ohv,
            merkle_witness,
            bitinject,
            randomness_index,
            randomness_commitment,
        };

        // we have this insert tail because we also support the update_or_insert operation. For that we do the big AND-tree for the ohv to determine whether we need to do an update or insert.
        //
        // Therefore we split the logic into AND-tree and tail.
        self.insert_tail(insert_tail, net0, net1, state0)
    }

    #[instrument(level = "debug", skip_all)]
    fn revoke_old_path(&mut self, mut key: Rep3RingShare<u32>, path_ohv: Vec<Rep3RingShare<Bit>>) {
        tracing::trace!("> revoke old path");
        let shift = LINEAR_SCAN_TREE_DEPTH - 1;
        self.layers[0].keys.push(key);
        let mut start = 0;
        for i in (0..self.layers.len()).skip(1) {
            key.a >>= 1;
            key.b >>= 1;
            let end = start + self.layers[i].keys.len();

            // Mark the other key as duplicate
            for (oh, key_) in izip!(path_ohv[start..end].iter(), self.layers[i].keys.iter_mut()) {
                key_.a.0 ^= u32::from(oh.a.convert().convert()) << shift;
                key_.b.0 ^= u32::from(oh.b.convert().convert()) << shift;
            }
            self.layers[i].keys.push(key.to_owned());
            start = end;
        }
        tracing::trace!("< revoke old path");
    }

    /// The insert-protocol without the AND-tree. May be called from either insert or update_or_insert.
    ///
    /// This method also computes the Poseidon2 traces for the insert proof.
    #[instrument(level = "debug", skip_all)]
    pub(crate) fn insert_tail<N: Rep3NetworkExt>(
        &mut self,
        tail: InsertTail,
        net0: &N,
        net1: &N,
        state0: &mut Rep3State,
    ) -> eyre::Result<InsertWithTrace> {
        tracing::debug!("starting insert-tail");
        let InsertTail {
            key,
            insert_value,
            path_ohv,
            merkle_witness,
            bitinject,
            randomness_index,
            randomness_commitment,
        } = tail;
        let mut proof_inputs = Vec::with_capacity(INSERT_PROOF_INPUTS);

        proof_inputs.push(Rep3AcvmType::from(ark_bn254::Fr::from(self.defaults[0])));
        proof_inputs.push(insert_value.into());
        for b in bitinject.iter() {
            proof_inputs.push(Rep3AcvmType::from(*b));
        }

        // An insert expects that the value is NOT present in the tree.
        // Therefore when building the poseidon hashes for the old root, we use the default value as old leaf value.
        let default_trivial_share = self.promote_default_value(net0);

        let poseidon2 = Poseidon2::<ark_bn254::Fr, 2, 5>::default();
        // Nothing we can parallelize with this unfortunately.
        let precompute = poseidon2.precompute_rep3(LINEAR_SCAN_TREE_DEPTH * 2 + 2, net0, state0)?;

        let poseidon_trace_input = PoseidonHashesWithTraceInput {
            new_value: insert_value,
            old_value: default_trivial_share,
            bitinject,
            merkle_witness,
            randomness_index,
            randomness_commitment,
            precompute,
        };
        let (_, poseidon_hashes_with_trace) = crate::join(
            || {
                self.revoke_old_path(key, path_ohv);
                eyre::Ok(())
            },
            || cosnark::poseidon_hashes_with_write_traces(poseidon_trace_input, net0),
        )?;
        let PoseidonHashesWithTrace {
            new_root,
            layer_values,
            proof_inputs: inputs,
            traces,
        } = poseidon_hashes_with_trace;

        proof_inputs.extend(inputs);
        // Last networking is to convert the computed values again to binary representation and open the new merkle-root.
        let (layer_values, root) =
            tracing::debug_span!("insert_tail::open_and_a2b").in_scope(|| {
                crate::join(
                    || conversion::a2b_many(&layer_values, net0, state0),
                    || arithmetic::open(new_root, net1),
                )
            })?;
        self.root = root;
        self.leaf_count += 1;
        self.total_count += LINEAR_SCAN_TREE_DEPTH;
        tracing::debug!("new root: {root}");
        tracing::debug!("leaf count: {}", self.leaf_count);
        tracing::debug!("total count count: {}", self.total_count);
        // Very last step, push the computed values in the storage
        self.push_new_values(layer_values);

        Ok(InsertWithTrace {
            inputs: proof_inputs,
            traces,
        })
    }
    /// Checks every layer for a match with the key, except the leaf layer.
    ///
    /// Insert doesn't need the leaf layer, because value MUST be not present on insert.
    pub(crate) fn find_path_skip_leaf_layer(
        &self,
        mut needle: Rep3RingShare<u32>,
    ) -> Vec<Rep3RingShare<u32>> {
        let mut result = Vec::with_capacity(self.total_count - self.leaf_count);
        for layer in self.layers.iter().skip(1) {
            needle.a >>= 1;
            needle.b >>= 1;
            for hay in layer.keys.iter() {
                result.push(hay ^ &needle);
            }
        }
        result
    }
}

impl LinearScanObliviousMap {
    /// Performs the insert-groth16 proof.
    #[instrument(level = "debug", skip_all)]
    pub(crate) fn groth16_insert_proof<N: Rep3NetworkExt>(
        &self,
        net0: &N,
        net1: &N,
        insert_with_trace: InsertWithTrace,
        state0: &mut Rep3State,
    ) -> eyre::Result<ObliviousWriteResult> {
        let InsertWithTrace { inputs, traces } = insert_with_trace;
        let (proof, public_inputs) =
            cosnark::noir_groth16(inputs, traces, &self.write_groth16, net0, net1, state0)?;
        debug_assert_eq!(public_inputs[1], self.inner.root);
        Ok(ObliviousWriteResult {
            proof,
            old_root: public_inputs[0],
            new_root: public_inputs[1],
            commitment_key: public_inputs[2],
            commitment_value: public_inputs[3],
        })
    }
}

impl ObliviousWriteResult {
    /// Returns the public inputs in a `Vec` in the correct order.
    pub fn inputs_to_vec(&self) -> Vec<ark_bn254::Fr> {
        vec![
            self.old_root,
            self.new_root,
            self.commitment_key,
            self.commitment_value,
        ]
    }
}

#[cfg(test)]
mod tests {

    use co_noir_to_r1cs::noir::r1cs;
    use itertools::izip;
    use mpc_core::protocols::{
        rep3::{self, Rep3State, conversion::A2BType},
        rep3_ring::{self, ring::ring_impl::RingElement},
    };
    use mpc_net::local::LocalNetwork;

    use crate::{
        LinearScanObliviousMap, ObliviousInsertRequest, ObliviousReadRequest,
        tests::groth16_material,
    };

    #[test]
    fn insert_then_read() -> eyre::Result<()> {
        const TEST_SUITE: usize = 10;
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
                let mut reads = Vec::with_capacity(TEST_SUITE);
                let mut inserts = Vec::with_capacity(TEST_SUITE);
                let mut defaults = Vec::with_capacity(TEST_SUITE);

                for (key, insert_value, r) in izip!(key_share0, value_share0, rand_share0) {
                    // read first on key before insert
                    let read_request = ObliviousReadRequest {
                        key,
                        randomness_commitment: r,
                    };
                    defaults.push(map.oblivious_read(read_request, &n0, &n3, &mut state)?);
                    let insert_req = ObliviousInsertRequest {
                        key,
                        insert_value,
                        randomness_index: r,
                        randomness_commitment: r,
                    };
                    inserts.push(map.oblivious_insert(insert_req, &n0, &n3, &mut state)?);
                    reads.push(map.oblivious_read(read_request, &n0, &n3, &mut state)?);
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

                for (key, insert_value, r) in izip!(key_share1, value_share1, rand_share1) {
                    // read first on key before insert
                    let read_request = ObliviousReadRequest {
                        key,
                        randomness_commitment: r,
                    };
                    defaults.push(map.oblivious_read(read_request, &n1, &n4, &mut state)?);
                    let insert_req = ObliviousInsertRequest {
                        key,
                        insert_value,
                        randomness_index: r,
                        randomness_commitment: r,
                    };
                    inserts.push(map.oblivious_insert(insert_req, &n1, &n4, &mut state)?);
                    reads.push(map.oblivious_read(read_request, &n1, &n4, &mut state)?);
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

                for (key, insert_value, r) in izip!(key_share2, value_share2, rand_share2) {
                    let read_request = ObliviousReadRequest {
                        key,
                        randomness_commitment: r,
                    };
                    // read first on key before insert
                    defaults.push(map.oblivious_read(read_request, &n2, &n5, &mut state)?);
                    let insert_req = ObliviousInsertRequest {
                        key,
                        insert_value,
                        randomness_index: r,
                        randomness_commitment: r,
                    };
                    inserts.push(map.oblivious_insert(insert_req, &n2, &n5, &mut state)?);
                    reads.push(map.oblivious_read(read_request, &n2, &n5, &mut state)?);
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

            assert!(r1cs::verify(
                &read_vk,
                &d0.proof,
                &[d0.root, d0.commitment]
            )?);
            assert!(r1cs::verify(
                &read_vk,
                &d1.proof,
                &[d1.root, d1.commitment]
            )?);
            assert!(r1cs::verify(
                &read_vk,
                &d2.proof,
                &[d2.root, d2.commitment]
            )?);
        }

        for (i0, i1, i2) in izip!(inserts0, inserts1, inserts2) {
            assert_eq!(i0.new_root, i1.new_root);
            assert_eq!(i1.new_root, i2.new_root);

            assert!(r1cs::verify(&write_vk, &i0.proof, &i0.inputs_to_vec())?);
            assert!(r1cs::verify(&write_vk, &i1.proof, &i1.inputs_to_vec())?);
            assert!(r1cs::verify(&write_vk, &i2.proof, &i2.inputs_to_vec())?);
        }

        for (r0, r1, r2, should_read) in izip!(reads0, reads1, reads2, values) {
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
