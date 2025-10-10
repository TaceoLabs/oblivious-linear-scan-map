use ark_ff::PrimeField;
use co_noir_to_r1cs::trace::MpcTraceHasher;
use itertools::{Itertools as _, izip};

use mpc_core::{
    gadgets::poseidon2::Poseidon2,
    protocols::{
        rep3::{
            Rep3BigUintShare, Rep3PrimeFieldShare, Rep3State, conversion, network::Rep3NetworkExt,
        },
        rep3_ring::{Rep3RingShare, ring::bit::Bit},
    },
};

use crate::{
    LINEAR_SCAN_TREE_DEPTH, LinearScanObliviousMap, NetworkRound1Result, ObliviousMembershipProof,
    ObliviousMerkleWitnessElement,
};

impl<F: PrimeField> LinearScanObliviousMap<F> {
    pub fn read_with_proof<N: Rep3NetworkExt>(
        &self,
        key: Rep3RingShare<u32>,
        net0: &N,
        net1: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<(Rep3PrimeFieldShare<F>, ObliviousMembershipProof<F>)> {
        let (read, path) = self.read(key, net0, net1, state)?;
        let hasher = Poseidon2::<F, 2, 5>::default();
        let mut hasher_precomputations =
            hasher.precompute_rep3(LINEAR_SCAN_TREE_DEPTH + 1, net0, state)?;
        let mut inputs = Vec::new();
        inputs.push(read.into());
        for p in path.0.iter() {
            inputs.push(p.position.into());
        }

        // hasher.hash_rep3_generate_noir_trace_many::<N, LINEAR_SCAN_TREE_DEPTH, LINEAR_SCAN_TREE_DEPTH>(
        //     path,
        //     &mut hasher_precomputations,
        //     net0,
        // )?;

        todo!()
    }

    pub fn read<N: Rep3NetworkExt>(
        &self,
        key: Rep3RingShare<u32>,
        net0: &N,
        net1: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<(Rep3PrimeFieldShare<F>, ObliviousMembershipProof<F>)> {
        // Per layer we have to compare the neighbor key to all elements to get the Merkle path. We also have to find the element in the first layer.
        let (key_bits, to_compare) = self.xor_read(key);

        let NetworkRound1Result(ohv_layer, bitinject) =
            Self::network_round1(&key_bits, to_compare, net0, net1, state)?;

        // TODO maybe find a way to dedup the code here
        let mut dots_a = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        // Start with finding the read element in the first layer
        dots_a.push(Self::dot(
            &ohv_layer[0..self.leaf_count],
            &self.layers[0].values,
            self.defaults[0],
            state,
        ));
        // Then find the path
        let mut start = self.leaf_count;
        for (layer, default) in izip!(self.layers.iter(), self.defaults) {
            let end = start + layer.keys.len();
            let dot = Self::dot(&ohv_layer[start..end], &layer.values, default, state);
            start = end;
            dots_a.push(dot);
        }
        let dots_b = net0.reshare_many(&dots_a)?;
        let dots = izip!(dots_a, dots_b)
            .map(|(a, b)| Rep3BigUintShare::<F>::new(a.into(), b.into()))
            .collect_vec();

        let dots = conversion::b2a_many(&dots, net0, state)?;
        let read = dots[0];

        let path = izip!(dots.into_iter().skip(1), bitinject)
            .map(|(other, position)| ObliviousMerkleWitnessElement { other, position })
            .collect_vec();

        Ok((read, ObliviousMembershipProof(path)))
    }

    fn xor_read(
        &self,
        key: Rep3RingShare<u32>,
    ) -> (Vec<Rep3RingShare<Bit>>, Vec<Rep3RingShare<u32>>) {
        // To find the element
        let (mut leaf_ohv, (key_bits, path)) = rayon::join(
            || self.find_in_leaves(key),
            || self.find_path_and_key_decompose(key),
        );
        leaf_ohv.extend(path);
        (key_bits, leaf_ohv)
    }

    fn find_in_leaves(&self, needle: Rep3RingShare<u32>) -> Vec<Rep3RingShare<u32>> {
        self.layers[0]
            .keys
            .iter()
            .map(|hay| hay ^ &needle)
            .collect_vec()
    }
}
