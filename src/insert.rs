use ark_ff::Zero as _;
use co_noir::{Bn254, Rep3AcvmType};
use co_noir_to_r1cs::noir::r1cs;
use co_noir_to_r1cs::trace::MpcTraceHasher;
use itertools::{Itertools as _, izip};
use mpc_core::{
    MpcState,
    gadgets::poseidon2::Poseidon2,
    protocols::{
        rep3::{
            self, Rep3PrimeFieldShare, Rep3State, arithmetic, conversion, network::Rep3NetworkExt,
        },
        rep3_ring::{Rep3RingShare, ring::bit::Bit},
    },
};

use crate::{Groth16Material, LINEAR_SCAN_TREE_DEPTH, LinearScanObliviousMap};

pub struct InsertWithTrace {
    inputs: Vec<Rep3AcvmType<ark_bn254::Fr>>,
    traces: Vec<Vec<Rep3AcvmType<ark_bn254::Fr>>>,
}

pub struct ObliviousInsertResult {
    pub new_root: ark_bn254::Fr,
    pub proof: ark_groth16::Proof<Bn254>,
    pub public_inputs: Vec<ark_bn254::Fr>,
}

impl LinearScanObliviousMap {
    #[expect(clippy::too_many_arguments)]
    pub fn oblivious_insert_threads<N: Rep3NetworkExt>(
        &mut self,
        key: Rep3RingShare<u32>,
        insert_value: Rep3PrimeFieldShare<ark_bn254::Fr>,
        net0: &N,
        net1: &N,
        randomness_index: Rep3PrimeFieldShare<ark_bn254::Fr>,
        randomness_commitment: Rep3PrimeFieldShare<ark_bn254::Fr>,
        state: &mut Rep3State,
    ) -> eyre::Result<ObliviousInsertResult> {
        let insert_with_trace = self.insert_threads(
            key,
            insert_value,
            net0,
            net1,
            randomness_index,
            randomness_commitment,
            state,
        )?;
        self.groth16_insert_proof(net0, net1, insert_with_trace, state)
    }

    #[expect(clippy::too_many_arguments)]
    pub fn oblivious_insert_seq<N: Rep3NetworkExt>(
        &mut self,
        key: Rep3RingShare<u32>,
        insert_value: Rep3PrimeFieldShare<ark_bn254::Fr>,
        net0: &N,
        net1: &N,
        randomness_index: Rep3PrimeFieldShare<ark_bn254::Fr>,
        randomness_commitment: Rep3PrimeFieldShare<ark_bn254::Fr>,
        state: &mut Rep3State,
    ) -> eyre::Result<ObliviousInsertResult> {
        let insert_with_trace = self.insert_thingy_seq(
            key,
            insert_value,
            net0,
            net1,
            randomness_index,
            randomness_commitment,
            state,
        )?;
        self.groth16_insert_proof(net0, net1, insert_with_trace, state)
    }

    #[expect(clippy::too_many_arguments)]
    pub fn insert_threads<N: Rep3NetworkExt>(
        &mut self,
        key: Rep3RingShare<u32>,
        insert_value: Rep3PrimeFieldShare<ark_bn254::Fr>,
        net0: &N,
        net1: &N,
        randomness_index: Rep3PrimeFieldShare<ark_bn254::Fr>,
        randomness_value: Rep3PrimeFieldShare<ark_bn254::Fr>,
        state0: &mut Rep3State,
    ) -> eyre::Result<InsertWithTrace> {
        let mut state1 = state0.fork(1).expect("cant fail for rep3");
        let mut proof_inputs = Vec::with_capacity(68);
        proof_inputs.push(Rep3AcvmType::from(ark_bn254::Fr::from(self.defaults[0])));
        proof_inputs.push(insert_value.into());
        let (path_ohv, bitinject, merkle_witness) = std::thread::scope(|s| {
            let s0 = s.spawn(|| {
                let path_ohv = self.find_path_skip_leaf_layer(key);
                let path_ohv = crate::rep3::is_zero_many(path_ohv, net0, state0)?;
                let key_bits = (0..32).map(|shift| (key >> shift).get_bit(0)).collect_vec();
                let bitinject =
                    crate::rep3::bit_inject_from_bits_to_field_many(&key_bits, net0, state0)?;
                for b in bitinject.iter() {
                    proof_inputs.push(Rep3AcvmType::from(*b));
                }
                eyre::Ok((path_ohv, bitinject))
            });
            // in parent thread start the witness loading
            let witness_ohv = self.find_witness(key);
            let witness_ohv = crate::rep3::is_zero_many(witness_ohv, net1, &mut state1)?;
            let merkle_witness = self.read_from_layers_with_ohv(&witness_ohv, net1, &mut state1)?;
            let (path_ohv, bitinject) = s0.join().expect("can join")?;
            eyre::Ok((path_ohv, bitinject, merkle_witness))
        })?;

        let default_trivial_share = rep3::arithmetic::promote_to_trivial_share(
            net0.id().try_into().expect("works for rep3 network"),
            self.defaults[0].into(),
        );
        let mut layer_values = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        let mut traces_new_root = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        let mut traces_old_root = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);

        // we need another thread scope to have a mut borrow
        let (new_root, index_trace, value_trace) = std::thread::scope(|s| {
            let revoke_old_path = s.spawn(|| self.revoke_old_path(key, path_ohv));

            // parent thread performs poseidon hashes in the meantime
            let poseidon2 = Poseidon2::<ark_bn254::Fr, 2, 5>::default();
            let mut poseidon2_precomputations =
                poseidon2.precompute_rep3(LINEAR_SCAN_TREE_DEPTH * 2 + 2, net0, state0)?;
            layer_values.push(insert_value);

            let mut current_value_new = insert_value;
            let mut current_value_old = default_trivial_share;

            // in the first run we also do the poseidon hashes for the two commitments

            // Calculate the commitment to the index
            let mut index = Rep3PrimeFieldShare::zero();
            for p in bitinject.iter().rev() {
                index += index;
                index += p;
            }

            let [left_new, right_new, left_old, right_old] = prep_poseidon(
                merkle_witness[0],
                current_value_new,
                current_value_old,
                bitinject[0],
                net0,
            )?;
            let ins = [
                left_new,
                right_new,
                left_old,
                right_old,
                index,
                randomness_index,
                insert_value,
                randomness_value,
            ];
            let (hashes, traces) = poseidon2.hash_rep3_generate_noir_trace_many::<_, 4, 8>(
                ins,
                &mut poseidon2_precomputations,
                net0,
            )?;
            let [new_trace, old_trace, index_trace, value_trace] = traces;
            proof_inputs.push(Rep3AcvmType::from(merkle_witness[0]));
            layer_values.push(hashes[0]);
            traces_new_root.push(new_trace);
            traces_old_root.push(old_trace);
            current_value_new = hashes[0];
            current_value_old = hashes[1];

            for (other, position) in izip!(merkle_witness, bitinject.clone()).skip(1) {
                let input =
                    prep_poseidon(other, current_value_new, current_value_old, position, net0)?;

                let (hashes, trace) = poseidon2.hash_rep3_generate_noir_trace_many::<_, 2, 4>(
                    input,
                    &mut poseidon2_precomputations,
                    net0,
                )?;
                let [new_trace, old_trace] = trace;
                proof_inputs.push(Rep3AcvmType::from(other));
                layer_values.push(hashes[0]);
                traces_new_root.push(new_trace);
                traces_old_root.push(old_trace);
                current_value_new = hashes[0];
                current_value_old = hashes[1];
            }
            revoke_old_path.join().expect("can join");
            eyre::Ok((current_value_new, index_trace, value_trace))
        })?;
        proof_inputs.push(Rep3AcvmType::from(randomness_index));
        proof_inputs.push(Rep3AcvmType::from(randomness_value));
        traces_old_root.extend(traces_new_root);
        traces_old_root.push(index_trace);
        traces_old_root.push(value_trace);

        std::thread::scope(|s| {
            let layer_values = s.spawn(|| conversion::a2b_many(&layer_values, net0, state0));

            self.root = arithmetic::open(new_root, net1)?;
            self.leaf_count += 1;
            self.total_count += LINEAR_SCAN_TREE_DEPTH;
            let layer_values = layer_values.join().expect("can join")?;
            for (layer, new_value) in izip!(self.layers.iter_mut(), layer_values.clone()) {
                layer.values.push(new_value.try_into().expect("Works"));
            }

            eyre::Ok(())
        })?;

        Ok(InsertWithTrace {
            inputs: proof_inputs,
            traces: traces_old_root,
        })
    }

    pub fn revoke_old_path(
        &mut self,
        mut key: Rep3RingShare<u32>,
        path_ohv: Vec<Rep3RingShare<Bit>>,
    ) {
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
    }

    #[expect(clippy::too_many_arguments)]
    pub fn insert_thingy_seq<N: Rep3NetworkExt>(
        &mut self,
        mut key: Rep3RingShare<u32>,
        insert_value: Rep3PrimeFieldShare<ark_bn254::Fr>,
        net0: &N,
        net1: &N,
        randomness_index: Rep3PrimeFieldShare<ark_bn254::Fr>,
        randomness_value: Rep3PrimeFieldShare<ark_bn254::Fr>,
        state: &mut Rep3State,
    ) -> eyre::Result<InsertWithTrace> {
        let (mut witness_ohv, path_ohv) = rayon::join(
            || self.find_witness(key),
            || self.find_path_skip_leaf_layer(key),
        );
        let key_bits = (0..32).map(|shift| (key >> shift).get_bit(0)).collect_vec();
        // TODO maybe have two threads again for this?
        witness_ohv.extend(path_ohv);

        let (mut witness_ohv, bitinject) = crate::rep3::is_zero_many_bitinject_parallel(
            &key_bits,
            witness_ohv,
            net0,
            net1,
            state,
        )?;

        // split the one-hot vectors for deduplication and index lookup
        let path_ohv = witness_ohv.split_off(self.total_count);

        let merkle_witness = self.read_from_layers_with_ohv(&witness_ohv, net0, state)?;

        let poseidon2 = Poseidon2::<ark_bn254::Fr, 2, 5>::default();

        // Add the new hashes per layer
        let mut poseidon2_precomputations =
            poseidon2.precompute_rep3(LINEAR_SCAN_TREE_DEPTH * 2 + 2, net0, state)?;
        let mut layer_values = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        let mut hash_path = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        let mut traces_insert = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        let mut traces_default = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        let mut current_value = insert_value;
        let mut current_value_default = rep3::arithmetic::promote_to_trivial_share(
            net0.id().try_into().expect("works for rep3 network"),
            ark_bn254::Fr::from(self.defaults[0]),
        );
        layer_values.push(insert_value);

        for (other, position) in izip!(merkle_witness, bitinject.clone()) {
            let left_a_n = (other - current_value) * position + current_value.a;
            let right_a_n = (current_value - other) * position + other.a;
            let left_a_d = (other - current_value_default) * position + current_value_default.a;
            let right_a_d = (current_value_default - other) * position + other.a;
            let bs = net0.reshare_many(&[left_a_n, right_a_n, left_a_d, right_a_d])?;
            let left_n = Rep3PrimeFieldShare::new(left_a_n, bs[0]);
            let right_n = Rep3PrimeFieldShare::new(right_a_n, bs[1]);
            let left_d = Rep3PrimeFieldShare::new(left_a_d, bs[2]);
            let right_d = Rep3PrimeFieldShare::new(right_a_d, bs[3]);
            // let poseidon_inputs_n = [left_n, right_n];
            // let poseidon_inputs_d = [left_d, right_d];
            let (hashes, trace) = poseidon2.hash_rep3_generate_noir_trace_many::<_, 2, 4>(
                [left_n, right_n, left_d, right_d],
                &mut poseidon2_precomputations,
                net0,
            )?;
            hash_path.push(Rep3AcvmType::from(other));
            layer_values.push(hashes[0]);
            let [insert_trace, default_trace] = trace;
            traces_insert.push(insert_trace);
            traces_default.push(default_trace);
            current_value = hashes[0];
            current_value_default = hashes[1];
        }

        let layer_values = conversion::a2b_many(&layer_values, net0, state)?;
        for (layer, new_value) in izip!(self.layers.iter_mut(), layer_values.clone()) {
            layer.values.push(new_value.try_into().expect("Works"));
        }
        self.leaf_count += 1;
        self.total_count += LINEAR_SCAN_TREE_DEPTH;
        self.root = arithmetic::open(current_value, net0)?;

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
        let mut inputs = Vec::with_capacity(68);
        inputs.push(ark_bn254::Fr::from(self.defaults[0]).into());
        inputs.push(insert_value.into());

        for p in bitinject.clone().into_iter() {
            inputs.push(p.into());
        }
        inputs.extend(hash_path);
        inputs.push(randomness_index.into());
        inputs.push(randomness_value.into());

        traces_default.extend(traces_insert);
        // do another trace for commitments

        // Calculate the commitment to the index
        let mut index = Rep3PrimeFieldShare::zero();
        for p in bitinject.iter().rev() {
            index += index;
            index += p;
        }
        let ins = [index, randomness_index, insert_value, randomness_value];
        let (_, trace) = poseidon2.hash_rep3_generate_noir_trace_many::<_, 2, 4>(
            ins,
            &mut poseidon2_precomputations,
            net0,
        )?;
        let [trace_index, trace_value] = trace;
        traces_default.push(trace_index);
        traces_default.push(trace_value);

        Ok(InsertWithTrace {
            traces: traces_default,
            inputs,
        })
    }

    fn groth16_insert_proof<N: Rep3NetworkExt>(
        &self,
        net0: &N,
        net1: &N,
        insert_with_trace: InsertWithTrace,
        state0: &mut Rep3State,
    ) -> eyre::Result<ObliviousInsertResult> {
        let InsertWithTrace { inputs, traces } = insert_with_trace;

        let Groth16Material {
            proof_schema,
            cs,
            pk,
        } = &self.write_groth16;

        let r1cs = r1cs::trace_to_r1cs_witness(inputs, traces, proof_schema, net0, net1, state0)?;
        let witness = r1cs::r1cs_witness_to_cogroth16(proof_schema, r1cs, state0.id);
        let (proof, public_inputs) = r1cs::prove(cs, pk, witness, net0, net1)?;
        Ok(ObliviousInsertResult {
            new_root: self.root,
            proof,
            public_inputs,
        })
    }

    fn find_path_skip_leaf_layer(&self, mut needle: Rep3RingShare<u32>) -> Vec<Rep3RingShare<u32>> {
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

fn oblivious_switch(
    lhs: Rep3PrimeFieldShare<ark_bn254::Fr>,
    rhs: Rep3PrimeFieldShare<ark_bn254::Fr>,
    selector: Rep3PrimeFieldShare<ark_bn254::Fr>,
) -> (ark_bn254::Fr, ark_bn254::Fr) {
    let left_a = (lhs - rhs) * selector + rhs.a;
    let right_a = (rhs - lhs) * selector + lhs.a;
    (left_a, right_a)
}

fn prep_poseidon<N: Rep3NetworkExt>(
    other: Rep3PrimeFieldShare<ark_bn254::Fr>,
    current_value_new: Rep3PrimeFieldShare<ark_bn254::Fr>,
    current_value_old: Rep3PrimeFieldShare<ark_bn254::Fr>,
    position: Rep3PrimeFieldShare<ark_bn254::Fr>,
    net: &N,
) -> eyre::Result<[Rep3PrimeFieldShare<ark_bn254::Fr>; 4]> {
    let (new_left, new_right) = oblivious_switch(other, current_value_new, position);
    let (old_left, old_right) = oblivious_switch(other, current_value_old, position);
    let bs = net.reshare_many(&[new_left, new_right, old_left, old_right])?;
    let left_new = Rep3PrimeFieldShare::new(new_left, bs[0]);
    let right_new = Rep3PrimeFieldShare::new(new_right, bs[1]);
    let left_old = Rep3PrimeFieldShare::new(old_left, bs[2]);
    let right_old = Rep3PrimeFieldShare::new(old_right, bs[3]);
    Ok([left_new, right_new, left_old, right_old])
}
