use ark_ff::{One as _, Zero as _};
use co_noir::{Bn254, Rep3AcvmType};
use co_noir_to_r1cs::noir::r1cs;
use co_noir_to_r1cs::trace::MpcTraceHasher;
use itertools::{Itertools as _, izip};

use mpc_core::{
    MpcState as _,
    gadgets::poseidon2::Poseidon2,
    protocols::{
        rep3::{
            self, Rep3BigUintShare, Rep3PrimeFieldShare, Rep3State, conversion,
            network::Rep3NetworkExt,
        },
        rep3_ring::{Rep3RingShare, ring::ring_impl::RingElement},
    },
};

use crate::{
    LINEAR_SCAN_TREE_DEPTH, LinearScanObliviousMap, ObliviousMerkleWitnessElement,
    groth16::Groth16Material,
};

struct ReadWithTrace {
    read_value: Rep3PrimeFieldShare<ark_bn254::Fr>,
    inputs: Vec<Rep3AcvmType<ark_bn254::Fr>>,
    traces: Vec<Vec<Rep3AcvmType<ark_bn254::Fr>>>,
}

struct PathAndWitness {
    path: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
    witness: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
    positions: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
}

pub struct ObliviousReadResult {
    pub read: Rep3PrimeFieldShare<ark_bn254::Fr>,
    pub proof: ark_groth16::Proof<Bn254>,
    pub public_inputs: Vec<ark_bn254::Fr>,
}

impl LinearScanObliviousMap {
    pub fn read<N: Rep3NetworkExt>(
        &self,
        key: Rep3RingShare<u32>,
        net0: &N,
        net1: &N,
        randomness_commitment: Rep3PrimeFieldShare<ark_bn254::Fr>,
        state0: &mut Rep3State,
    ) -> eyre::Result<ObliviousReadResult> {
        let path_and_witness = self.read_path_and_witness(key, net0, net1, state0)?;
        let trace =
            self.read_build_execution_trace(net0, path_and_witness, randomness_commitment, state0)?;
        self.groth16_read_proof(net0, net1, trace, state0)
    }

    fn groth16_read_proof<N: Rep3NetworkExt>(
        &self,
        net0: &N,
        net1: &N,
        read_with_trace: ReadWithTrace,
        state0: &mut Rep3State,
    ) -> eyre::Result<ObliviousReadResult> {
        let ReadWithTrace {
            read_value,
            inputs,
            traces,
        } = read_with_trace;

        let Groth16Material {
            proof_schema,
            cs,
            pk,
        } = &self.read_groth16;

        let r1cs = r1cs::trace_to_r1cs_witness(inputs, traces, proof_schema, net0, net1, state0)?;

        let witness = r1cs::r1cs_witness_to_cogroth16(proof_schema, r1cs, state0.id);
        let (proof, public_inputs) = r1cs::prove(cs, pk, witness, net0, net1)?;
        Ok(ObliviousReadResult {
            read: read_value,
            proof,
            public_inputs,
        })
    }

    fn read_path_and_witness<N: Rep3NetworkExt>(
        &self,
        key: Rep3RingShare<u32>,
        net0: &N,
        net1: &N,
        state0: &mut Rep3State,
    ) -> eyre::Result<PathAndWitness> {
        let mut state1 = state0.fork(1).expect("cannot fail for rep3");
        let (path, (witness, positions)) = std::thread::scope(|s| {
            let read_path = s.spawn(|| self.read_path(key, net0, state0));
            let witness = s.spawn(|| self.read_merkle_witness(key, net1, &mut state1));
            let path = read_path.join().expect("can join")?;
            let witness = witness.join().expect("can join")?;
            eyre::Ok((path, witness))
        })?;
        Ok(PathAndWitness {
            path,
            witness,
            positions,
        })
    }

    fn read_build_execution_trace<N: Rep3NetworkExt>(
        &self,
        net: &N,
        path_and_witness: PathAndWitness,
        randomness_commitment: Rep3PrimeFieldShare<ark_bn254::Fr>,
        state: &mut Rep3State,
    ) -> eyre::Result<ReadWithTrace> {
        let PathAndWitness {
            path,
            witness,
            positions,
        } = path_and_witness;

        let mut proof_inputs = Vec::with_capacity(65);
        let read_value = path[0];

        proof_inputs.push(read_value.into());
        for p in positions.clone().into_iter() {
            proof_inputs.push(p.into());
        }

        let hasher = Poseidon2::<ark_bn254::Fr, 2, 5>::default();
        let mut hasher_precomputations =
            hasher.precompute_rep3(LINEAR_SCAN_TREE_DEPTH + 1, net, state)?;

        debug_assert_eq!(path.len(), witness.len());
        let hashes = izip!(path.iter(), witness.iter())
            .map(|(p, w)| w - p)
            .collect_vec();

        let switches = rep3::arithmetic::mul_vec(&positions, &hashes, net, state)?;

        let mut merkle_membership = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        let mut ins = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH * 2);
        for (p, w, mul, position) in
            izip!(path.clone(), witness.clone(), switches, positions.clone())
        {
            proof_inputs.push(w.into());
            let hash_left = mul + p;
            let hash_right = w - mul;
            ins.push(hash_left);
            ins.push(hash_right);
            merkle_membership.push(ObliviousMerkleWitnessElement { other: w, position });
        }
        // Calculate the commitment to the index
        let mut index = Rep3PrimeFieldShare::zero();
        for p in positions.iter().rev() {
            index += index;
            index += p;
        }
        ins.push(index);
        ins.push(randomness_commitment);
        proof_inputs.push(randomness_commitment.into());

        let (_, traces) = hasher.hash_rep3_generate_noir_trace_many::<_, 33, 66>(
            ins.try_into().expect("works"),
            &mut hasher_precomputations,
            net,
        )?;
        Ok(ReadWithTrace {
            read_value,
            inputs: proof_inputs,
            traces: traces.to_vec(),
        })
    }

    pub fn read_path<N: Rep3NetworkExt>(
        &self,
        key: Rep3RingShare<u32>,
        net: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>> {
        let path_ohv = crate::rep3::is_zero_many(self.find_path(key), net, state)?;
        let mut dots_a = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        let mut start = 0;
        for (layer, default) in izip!(self.layers.iter(), self.defaults.into_iter()) {
            let end = start + layer.keys.len();
            let dot = Self::dot(&path_ohv[start..end], &layer.values, default, state);
            start = end;
            dots_a.push(dot);
        }
        let dots_b = net.reshare_many(&dots_a)?;
        let dots = izip!(dots_a, dots_b)
            .map(|(a, b)| Rep3BigUintShare::<ark_bn254::Fr>::new(a.into(), b.into()))
            .collect_vec();

        let dots = conversion::b2a_many(&dots, net, state)?;

        Ok(dots)
    }

    pub fn read_path_dots_mt<N: Rep3NetworkExt>(
        &self,
        key: Rep3RingShare<u32>,
        net: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>> {
        let path_ohv = crate::rep3::is_zero_many(self.find_path(key), net, state)?;
        let mut dots_a = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        let mut start = 0;
        let mut offsets = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        for layer in self.layers.iter() {
            let end = start + layer.keys.len();
            offsets.push((start, end));
            start = end;
        }
        for (layer, default, (start, end)) in izip!(
            self.layers.iter(),
            self.defaults.into_iter(),
            offsets.into_iter()
        ) {
            let dot = Self::dot(&path_ohv[start..end], &layer.values, default, state);
            dots_a.push(dot);
        }
        let dots_b = net.reshare_many(&dots_a)?;
        let dots = izip!(dots_a, dots_b)
            .map(|(a, b)| Rep3BigUintShare::<ark_bn254::Fr>::new(a.into(), b.into()))
            .collect_vec();

        let dots = conversion::b2a_many(&dots, net, state)?;

        Ok(dots)
    }

    #[expect(clippy::type_complexity)]
    pub fn read_merkle_witness<N: Rep3NetworkExt>(
        &self,
        key: Rep3RingShare<u32>,
        net: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<(
        Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
        Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
    )> {
        // Per layer we have to compare the neighbor key to all elements to get the Merkle path. We also have to find the element in the first layer.
        let witness_ohv = self.find_witness(key);
        let key_bits = (0..32).map(|shift| (key >> shift).get_bit(0)).collect_vec();

        // we could maybe parallelize this with another network, but the bitinject is negligible in contrast to the AND-tree and poseidon hashes, therefore we stick with one two networks.
        let ohv_layer = crate::rep3::is_zero_many(witness_ohv, net, state)?;
        let bitinject = crate::rep3::bit_inject_from_bits_to_field_many(&key_bits, net, state)?;

        let mut dots_a = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        let mut start = 0;
        for (layer, default) in izip!(self.layers.iter(), self.defaults) {
            let end = start + layer.keys.len();
            let dot = Self::dot(&ohv_layer[start..end], &layer.values, default, state);
            start = end;
            dots_a.push(dot);
        }
        let dots_b = net.reshare_many(&dots_a)?;
        let dots = izip!(dots_a, dots_b)
            .map(|(a, b)| Rep3BigUintShare::new(a.into(), b.into()))
            .collect_vec();

        let dots = conversion::b2a_many(&dots, net, state)?;

        Ok((dots, bitinject))
    }

    fn find_path(&self, mut needle: Rep3RingShare<u32>) -> Vec<Rep3RingShare<u32>> {
        // To find the path
        let mut path_ohv = Vec::with_capacity(self.total_count);
        for layer in self.layers.iter() {
            for hay in layer.keys.iter() {
                path_ohv.push(hay ^ &needle);
            }

            needle.a >>= 1;
            needle.b >>= 1;
        }
        path_ohv
    }

    fn find_witness(&self, mut needle: Rep3RingShare<u32>) -> Vec<Rep3RingShare<u32>> {
        // To find the path
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
}
