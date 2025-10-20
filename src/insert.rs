use itertools::izip;
use mpc_core::{
    gadgets::poseidon2::Poseidon2,
    protocols::{
        rep3::{Rep3PrimeFieldShare, Rep3State, arithmetic, conversion, network::Rep3NetworkExt},
        rep3_ring::{Rep3RingShare, ring::bit::Bit},
    },
};

use crate::{
    LINEAR_SCAN_TREE_DEPTH, LinearScanObliviousMap, NetworkRound1Result, ObliviousMembershipProof,
};

impl LinearScanObliviousMap {
    fn insert<N: Rep3NetworkExt>(
        &mut self,
        mut key: Rep3RingShare<u32>,
        value: Rep3PrimeFieldShare<ark_bn254::Fr>,
        net0: &N,
        net1: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<ObliviousMembershipProof> {
        let (key_bits, to_compare) = self.xor_insert(key);

        let NetworkRound1Result(mut ohv_path, bitinject) =
            Self::network_round1(&key_bits, to_compare, net0, net1, state)?;
        // split the one-hot vectors for deduplication and index lookup
        let ohv_dedup = ohv_path.split_off(self.total_count);

        let path = self.compute_merkle_path(&ohv_path, bitinject, net0, state)?;

        let poseidon2 = Poseidon2::<ark_bn254::Fr, 2, 5>::default();

        // Add the new hashes per layer
        let mut poseidon2_precomputations =
            poseidon2.precompute_rep3(LINEAR_SCAN_TREE_DEPTH, net0, state)?;
        let mut layer_values = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        let mut current_value = value;
        for p in path.iter() {
            layer_values.push(current_value);
            current_value = Self::poseidon2_cmux(
                p,
                current_value,
                net0,
                &poseidon2,
                &mut poseidon2_precomputations,
            )?;
        }

        let layer_values = conversion::a2b_many(&layer_values, net0, state)?;
        for (layer, new_value) in self.layers.iter_mut().zip(layer_values.into_iter()) {
            layer.values.push(new_value.try_into().expect("Works"));
        }

        std::thread::scope(|s| {
            let root = s.spawn(|| arithmetic::open(current_value, net0));

            // TODO we can move this up and do it during poseidon2 cmux
            // Add the new key and deduplicate any similar ones
            let shift = LINEAR_SCAN_TREE_DEPTH - 1;
            self.layers[0].keys.push(key);
            let mut start = 0;
            for i in (0..self.layers.len()).skip(1) {
                key.a >>= 1;
                key.b >>= 1;
                let end = start + self.layers[i].keys.len();

                // Mark the other key as duplicate
                for (oh, key_) in
                    izip!(ohv_dedup[start..end].iter(), self.layers[i].keys.iter_mut())
                {
                    key_.a.0 ^= u32::from(oh.a.convert().convert()) << shift;
                    key_.b.0 ^= u32::from(oh.b.convert().convert()) << shift;
                }
                self.layers[i].keys.push(key.to_owned());
                start = end;
            }

            self.leaf_count += 1;
            self.total_count += LINEAR_SCAN_TREE_DEPTH;
            self.root = root.join().expect("can join")?;
            eyre::Ok(())
        })?;

        Ok(ObliviousMembershipProof(path))
    }

    fn xor_insert(
        &self,
        key: Rep3RingShare<u32>,
    ) -> (Vec<Rep3RingShare<Bit>>, Vec<Rep3RingShare<u32>>) {
        // To find the element
        let (dedups, (key_bits, mut path)) = rayon::join(
            || self.find_path_skip_leaves(key),
            || self.find_path_and_key_decompose(key),
        );
        path.extend(dedups);
        (key_bits, path)
    }

    fn find_path_skip_leaves(&self, mut needle: Rep3RingShare<u32>) -> Vec<Rep3RingShare<u32>> {
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
