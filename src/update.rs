use co_noir::Rep3AcvmType;
use itertools::Itertools;
use mpc_core::{
    MpcState as _,
    gadgets::poseidon2::Poseidon2,
    protocols::{
        rep3::{Rep3PrimeFieldShare, Rep3State, conversion, network::Rep3NetworkExt},
        rep3_ring::{Rep3RingShare, ring::bit::Bit},
    },
};
use rayon::prelude::*;
use tracing::instrument;

use crate::{
    INSERT_PROOF_INPUTS, LINEAR_SCAN_TREE_DEPTH, Rep3BigIntShare,
    base::{MapBase, PoseidonHashesWithTrace, PoseidonHashesWithTraceInput},
    cosnark::{self, InsertWithTrace},
};

pub struct ObliviousUpdateRequest {
    pub key: Rep3RingShare<u32>,
    pub update_value: Rep3PrimeFieldShare<ark_bn254::Fr>,
    pub randomness_index: Rep3PrimeFieldShare<ark_bn254::Fr>,
    pub randomness_commitment: Rep3PrimeFieldShare<ark_bn254::Fr>,
}

pub(super) struct UpdateTail {
    pub(super) update_value: Rep3PrimeFieldShare<ark_bn254::Fr>,
    pub(super) path_ohv: Vec<Rep3RingShare<Bit>>,
    pub(super) merkle_witness: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
    pub(super) bitinject: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
    pub(super) randomness_index: Rep3PrimeFieldShare<ark_bn254::Fr>,
    pub(super) randomness_commitment: Rep3PrimeFieldShare<ark_bn254::Fr>,
}

impl MapBase {
    #[instrument(level = "debug", skip_all)]
    pub(super) fn update<N: Rep3NetworkExt>(
        &mut self,
        update_request: ObliviousUpdateRequest,
        net0: &N,
        net1: &N,
        state0: &mut Rep3State,
    ) -> eyre::Result<InsertWithTrace> {
        let ObliviousUpdateRequest {
            key,
            update_value,
            randomness_index,
            randomness_commitment,
        } = update_request;
        let mut state1 = state0.fork(1).expect("cant fail for rep3");
        let (path_ohv, (merkle_witness, bitinject)) =
            tracing::debug_span!("update::read_path_and_witness").in_scope(|| {
                crate::join(
                    || {
                        let path_ohv = self.find_path(key);
                        crate::mpc::is_zero_many(path_ohv, net0, state0)
                    },
                    || {
                        let witness = self.read_merkle_witness(key, net1, &mut state1)?;
                        let bitinject = Self::key_decompose(key, net1, &mut state1)?;
                        Ok((witness, bitinject))
                    },
                )
            })?;
        let update_tail = UpdateTail {
            update_value,
            path_ohv,
            merkle_witness,
            bitinject,
            randomness_index,
            randomness_commitment,
        };
        // we have this update tail because we also support the update_or_insert operation. For that we do the big AND-tree for the ohv to determine whether we need to do an update or insert.
        //
        // Therefore we split the logic into AND-tree and tail.
        self.update_tail(update_tail, net0, net1, state0, &mut state1)
    }

    #[instrument(level = "debug", skip_all)]
    pub(super) fn update_tail<N: Rep3NetworkExt>(
        &mut self,
        update_tail: UpdateTail,
        net0: &N,
        net1: &N,
        state0: &mut Rep3State,
        state1: &mut Rep3State,
    ) -> eyre::Result<InsertWithTrace> {
        tracing::debug!("starting update-tail");
        let UpdateTail {
            update_value,
            path_ohv,
            merkle_witness,
            bitinject,
            randomness_index,
            randomness_commitment,
        } = update_tail;

        let (old_value, precompute) = crate::join(
            || self.read_from_leaf_layer(&path_ohv, net0, state0),
            || {
                let poseidon2 = Poseidon2::<ark_bn254::Fr, 2, 5>::default();
                poseidon2.precompute_rep3(LINEAR_SCAN_TREE_DEPTH * 2 + 2, net1, state1)
            },
        )?;
        let mut proof_inputs = Vec::with_capacity(INSERT_PROOF_INPUTS);

        proof_inputs.push(Rep3AcvmType::from(old_value));
        proof_inputs.push(Rep3AcvmType::from(update_value));
        for b in bitinject.iter() {
            proof_inputs.push(Rep3AcvmType::from(*b));
        }

        let poseidon_trace_input = PoseidonHashesWithTraceInput {
            new_value: update_value,
            old_value,
            bitinject,
            merkle_witness,
            randomness_index,
            randomness_commitment,
            precompute,
        };
        let poseidon_hashes_with_trace =
            cosnark::poseidon_hashes_with_write_traces(poseidon_trace_input, net0)?;

        let PoseidonHashesWithTrace {
            new_root,
            layer_values,
            proof_inputs: inputs,
            traces,
        } = poseidon_hashes_with_trace;

        proof_inputs.extend(inputs);

        let layer_values = conversion::a2b_many(&layer_values, net0, state0)?;
        let _span_guard = tracing::debug_span!("update database").entered();

        // multithread the update per layer
        let ranges = self
            .layers
            .iter()
            .scan(0, |offset, layer| {
                let start = *offset;
                let end = start + layer.values.len();
                *offset = end;
                Some((start, end))
            })
            .collect_vec();

        // Update the full database, essentially a big cmux
        let mut to_reshare = (self.layers.par_iter(), layer_values, ranges.par_iter())
            .into_par_iter()
            .flat_map(|(layer, new_value, (start, end))| {
                let new_value =
                    Rep3BigIntShare::<ark_bn254::Fr>::try_from(new_value).expect("Works");
                let mut to_reshare = Vec::with_capacity(layer.values.len());

                for (value, ohv) in layer.values.iter().zip(path_ohv[*start..*end].iter()) {
                    // Add the cmux: If ohv == 0, we keep the old value, else we update it
                    let other = new_value ^ value;
                    let mut cmux = value.a.to_owned();
                    // This is the AND-gate protocol ohv_ & other
                    if ohv.a.0.convert() {
                        cmux ^= other.a ^ other.b;
                    }
                    if ohv.b.0.convert() {
                        cmux ^= other.a;
                    }
                    to_reshare.push(cmux);
                }
                to_reshare
            })
            .collect::<Vec<_>>();

        // Reshare also the root
        to_reshare.push(new_root.b.into());
        // Put the new values in
        let mut reshared = net0.reshare_many(&to_reshare)?;
        (self.layers.par_iter_mut(), ranges)
            .into_par_iter()
            .for_each(|(layer, (start, end))| {
                for (value, (a, b)) in layer.values.iter_mut().zip(
                    to_reshare[start..end]
                        .iter()
                        .zip(reshared[start..end].iter()),
                ) {
                    value.a = *a;
                    value.b = *b;
                }
            });

        // Update the root
        self.root =
            ark_bn254::Fr::from(reshared.pop().expect("is there")) + new_root.a + new_root.b;

        Ok(InsertWithTrace {
            inputs: proof_inputs,
            traces,
        })
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
        ObliviousUpdateRequest, tests::groth16_material,
    };

    #[test]
    fn insert_update_then_read() -> eyre::Result<()> {
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
                    let insert_req = ObliviousInsertRequest {
                        key,
                        insert_value,
                        randomness_index: r,
                        randomness_commitment: r,
                    };
                    let update_req = ObliviousUpdateRequest {
                        key,
                        update_value,
                        randomness_index: r,
                        randomness_commitment: r,
                    };
                    inserts.push(map.oblivious_insert(insert_req, &n0, &n3, &mut state)?);
                    read_after_insert.push(map.oblivious_read(
                        read_request,
                        &n0,
                        &n3,
                        &mut state,
                    )?);
                    updates.push(map.oblivious_update(update_req, &n0, &n3, &mut state)?);
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
                    let insert_req = ObliviousInsertRequest {
                        key,
                        insert_value,
                        randomness_index: r,
                        randomness_commitment: r,
                    };
                    let update_req = ObliviousUpdateRequest {
                        key,
                        update_value,
                        randomness_index: r,
                        randomness_commitment: r,
                    };
                    inserts.push(map.oblivious_insert(insert_req, &n1, &n4, &mut state)?);
                    read_after_insert.push(map.oblivious_read(
                        read_request,
                        &n1,
                        &n4,
                        &mut state,
                    )?);
                    updates.push(map.oblivious_update(update_req, &n1, &n4, &mut state)?);
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
                    let insert_req = ObliviousInsertRequest {
                        key,
                        insert_value,
                        randomness_index: r,
                        randomness_commitment: r,
                    };
                    let update_req = ObliviousUpdateRequest {
                        key,
                        update_value,
                        randomness_index: r,
                        randomness_commitment: r,
                    };
                    inserts.push(map.oblivious_insert(insert_req, &n2, &n5, &mut state)?);
                    read_after_insert.push(map.oblivious_read(
                        read_request,
                        &n2,
                        &n5,
                        &mut state,
                    )?);
                    updates.push(map.oblivious_update(update_req, &n2, &n5, &mut state)?);
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
