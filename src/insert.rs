use ark_ff::Zero as _;
use co_noir::{Bn254, Rep3AcvmType};
use co_noir_to_r1cs::noir::r1cs;
use co_noir_to_r1cs::trace::MpcTraceHasher;
use itertools::{Itertools as _, izip};
use mpc_core::{
    gadgets::poseidon2::Poseidon2,
    protocols::{
        rep3::{Rep3PrimeFieldShare, Rep3State, arithmetic, conversion, network::Rep3NetworkExt},
        rep3_ring::Rep3RingShare,
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
    pub fn oblivious_insert<N: Rep3NetworkExt>(
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
        let mut current_value_default =
            mpc_core::protocols::rep3::arithmetic::promote_to_trivial_share(
                net0.id().try_into().expect("works"),
                ark_bn254::Fr::from(self.defaults[0]),
            );
        layer_values.push(insert_value);

        for (other, position) in izip!(merkle_witness, bitinject.clone()) {
            let left_a_n = (other - current_value) * position + current_value.a;
            let right_a_n = (current_value - other) * position + other.a;
            let left_a_d = (other - current_value_default) * position + current_value.a;
            let right_a_d = (current_value_default - other) * position + other.a;
            let bs = net0.reshare_many(&[left_a_n, right_a_n, left_a_d, right_a_d])?;
            let left_n = Rep3PrimeFieldShare::new(left_a_n, bs[0]);
            let right_n = Rep3PrimeFieldShare::new(right_a_n, bs[1]);
            let left_d = Rep3PrimeFieldShare::new(left_a_n, bs[2]);
            let right_d = Rep3PrimeFieldShare::new(right_a_n, bs[3]);
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
        let old_root = self.root;
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
        inputs.push(old_root.into());
        inputs.push(self.root.into());

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

        println!("inputs len: {}", inputs.len());
        println!("traces len: {}", traces.len());
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
