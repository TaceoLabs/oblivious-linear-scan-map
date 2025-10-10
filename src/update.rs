use mpc_core::{
    gadgets::poseidon2::Poseidon2,
    protocols::{
        rep3::{Rep3PrimeFieldShare, Rep3State, arithmetic, conversion, network::Rep3NetworkExt},
        rep3_ring::{Rep3RingShare, ring::bit::Bit},
    },
};

use crate::{
    DELETED_LEAF_VALUE, LINEAR_SCAN_TREE_DEPTH, LinearScanObliviousMap, NetworkRound1Result,
    ObliviousMembershipProof,
};

impl LinearScanObliviousMap {
    pub fn update<N: Rep3NetworkExt>(
        &mut self,
        key: Rep3RingShare<u32>,
        value: Rep3PrimeFieldShare<ark_bn254::Fr>,
        net0: &N,
        net1: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<ObliviousMembershipProof> {
        let (key_bits, to_compare) = self.xor_update(key);
        let NetworkRound1Result(mut ohv_updates, bitinject) =
            Self::network_round1(&key_bits, to_compare, net0, net1, state)?;
        let ohv_path = ohv_updates.split_off(self.total_count);

        let path = self.compute_merkle_path(&ohv_path, bitinject, net0, state)?;
        let poseidon2 = Poseidon2::<ark_bn254::Fr, 2, 5>::default();

        // Calculate the new hashes per layer
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

        // Update the full database, essentially a big cmux
        let mut to_reshare = Vec::with_capacity(self.total_count);
        let mut start = 0;
        for (layer, new_value) in self.layers.iter().zip(layer_values) {
            let end = start + layer.values.len();
            let new_value = new_value.try_into().expect("Works");

            for (value, ohv) in layer.values.iter().zip(ohv_updates[start..end].iter()) {
                // Add the cmux: If ohv == 0, we keep the old value, else we update it
                let other = &new_value ^ value;
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
            start = end;
        }
        // Reshare also the root
        to_reshare.push(current_value.b.into());
        // Put the new values in
        let mut reshared = net0.reshare_many(&to_reshare)?;
        let mut start = 0;
        for layer in self.layers.iter_mut() {
            let end = start + layer.values.len();
            for (value, (a, b)) in layer.values.iter_mut().zip(
                to_reshare[start..end]
                    .iter()
                    .zip(reshared[start..end].iter()),
            ) {
                value.a = *a;
                value.b = *b;
            }
            start = end;
        }

        // Update the root
        self.root =
            ark_bn254::Fr::from(reshared.pop().unwrap()) + current_value.a + current_value.b;

        Ok(ObliviousMembershipProof(path))
    }
    pub fn delete<N: Rep3NetworkExt>(
        &mut self,
        key: Rep3RingShare<u32>,
        net0: &N,
        net1: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<ObliviousMembershipProof> {
        // The value in update is only ever used in CMUXes with a secret share, so we can not get any performance advantage by knowing this value in plain. Thus we just use the update protocol.
        let deadbeef =
            arithmetic::promote_to_trivial_share(state.id, ark_bn254::Fr::from(DELETED_LEAF_VALUE));
        self.update(key, deadbeef, net0, net1, state)
    }

    fn xor_update(
        &self,
        key: Rep3RingShare<u32>,
    ) -> (Vec<Rep3RingShare<Bit>>, Vec<Rep3RingShare<u32>>) {
        // To find the element
        let (mut updates, (key_bits, path)) = rayon::join(
            || self.find_path_u(key),
            || self.find_path_and_key_decompose(key),
        );
        updates.extend(path);
        (key_bits, updates)
    }

    fn find_path_u(&self, mut needle: Rep3RingShare<u32>) -> Vec<Rep3RingShare<u32>> {
        let mut result = Vec::with_capacity(self.total_count - self.leaf_count);
        for layer in self.layers.iter() {
            for hay in layer.keys.iter() {
                result.push(hay ^ &needle);
            }
            needle.a >>= 1;
            needle.b >>= 1;
        }
        result
    }
}
