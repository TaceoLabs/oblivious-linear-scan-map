use ark_ff::{One as _, PrimeField};
use itertools::{Itertools as _, izip};
use mpc_core::{
    MpcState,
    gadgets::poseidon2::{Poseidon2, Poseidon2Precomputations},
    protocols::{
        rep3::{
            Rep3BigUintShare, Rep3PrimeFieldShare, Rep3State, arithmetic, conversion, id::PartyID,
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
pub mod rep3;

pub const DELETED_LEAF_VALUE: u64 = 0xDEADBEEF;
pub const LINEAR_SCAN_TREE_DEPTH: usize = 32;

pub struct ObliviousMembershipProof<F: PrimeField>(pub Vec<ObliviousMerkleWitnessElement<F>>);

struct NetworkRound1Result<F: PrimeField>(Vec<Rep3RingShare<Bit>>, Vec<Rep3PrimeFieldShare<F>>);

#[derive(Debug, Clone)]
/// A witness of proving one layer in a Merkle tree.
pub struct ObliviousMerkleWitnessElement<F: PrimeField> {
    /// Determines the other value required to compute the hash for the next layer.
    pub other: Rep3PrimeFieldShare<F>,
    /// Determines the position for the prove element in the hash for current layer.
    pub position: Rep3PrimeFieldShare<F>, // Index of the prove element
}

#[derive(Default, Clone)]
pub(crate) struct Layer<F: PrimeField> {
    keys: Vec<Rep3RingShare<u32>>,
    values: Vec<Rep3BigIntShare<F>>,
}

pub struct LinearScanObliviousMap<F: PrimeField> {
    layers: [Layer<F>; LINEAR_SCAN_TREE_DEPTH],
    leaf_count: usize,
    total_count: usize,
    defaults: [F::BigInt; LINEAR_SCAN_TREE_DEPTH],
    root: F,
}

impl<F: PrimeField> Default for LinearScanObliviousMap<F> {
    fn default() -> Self {
        Self::new()
    }
}

impl<F: PrimeField> LinearScanObliviousMap<F> {
    pub fn new() -> Self {
        Self::with_default_value(F::from(0))
    }

    pub fn with_default_value(mut default_value: F) -> Self {
        let poseidon2 = Poseidon2::<F, 2, 5>::default();
        let defaults = std::array::from_fn(|_| {
            let prev = default_value.into_bigint();
            default_value += poseidon2.permutation(&[default_value, default_value])[0];
            prev
        });
        Self {
            layers: std::array::from_fn(|_| Layer::default()),
            leaf_count: 0,
            total_count: 0,
            defaults,
            root: default_value,
        }
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

    pub fn insert<N: Rep3NetworkExt>(
        &mut self,
        mut key: Rep3RingShare<u32>,
        value: Rep3PrimeFieldShare<F>,
        net0: &N,
        net1: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<ObliviousMembershipProof<F>> {
        let (key_bits, to_compare) = self.xor_insert(key);

        let NetworkRound1Result(mut ohv_path, bitinject) =
            Self::network_round1(&key_bits, to_compare, net0, net1, state)?;
        // split the one-hot vectors for deduplication and index lookup
        let ohv_dedup = ohv_path.split_off(self.total_count);

        let path = self.compute_merkle_path(&ohv_path, bitinject, net0, state)?;

        let poseidon2 = Poseidon2::<F, 2, 5>::default();

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

    pub fn update<N: Rep3NetworkExt>(
        &mut self,
        key: Rep3RingShare<u32>,
        value: Rep3PrimeFieldShare<F>,
        net0: &N,
        net1: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<ObliviousMembershipProof<F>> {
        let (key_bits, to_compare) = self.xor_update(key);
        let NetworkRound1Result(mut ohv_updates, bitinject) =
            Self::network_round1(&key_bits, to_compare, net0, net1, state)?;
        let ohv_path = ohv_updates.split_off(self.total_count);

        let path = self.compute_merkle_path(&ohv_path, bitinject, net0, state)?;
        let poseidon2 = Poseidon2::<F, 2, 5>::default();

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
        self.root = F::from(reshared.pop().unwrap()) + current_value.a + current_value.b;

        Ok(ObliviousMembershipProof(path))
    }

    #[inline(always)]
    pub fn depth(&self) -> usize {
        LINEAR_SCAN_TREE_DEPTH
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

    fn xor_update(
        &self,
        key: Rep3RingShare<u32>,
    ) -> (Vec<Rep3RingShare<Bit>>, Vec<Rep3RingShare<u32>>) {
        // To find the element
        let (mut updates, (key_bits, path)) = rayon::join(
            || self.find_path(key),
            || self.find_path_and_key_decompose(key),
        );
        updates.extend(path);
        (key_bits, updates)
    }

    fn find_in_leaves(&self, needle: Rep3RingShare<u32>) -> Vec<Rep3RingShare<u32>> {
        self.layers[0]
            .keys
            .iter()
            .map(|hay| hay ^ &needle)
            .collect_vec()
    }

    fn find_path(&self, mut needle: Rep3RingShare<u32>) -> Vec<Rep3RingShare<u32>> {
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

    // finds the path of the member (its neighbors)
    fn find_path_and_key_decompose(
        &self,
        mut needle: Rep3RingShare<u32>,
    ) -> (Vec<Rep3RingShare<Bit>>, Vec<Rep3RingShare<u32>>) {
        // To find the path
        let mut to_compare = Vec::with_capacity(self.total_count);
        let mut key_bits = Vec::with_capacity(32);
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
        other: &[Rep3BigIntShare<F>],
        default: F::BigInt,
        state: &mut Rep3State,
    ) -> F::BigInt {
        debug_assert_eq!(
            ohv.len(),
            other.len(),
            "The length of the two vectors must be equal"
        );

        // Set the default value:
        // Assuming only one element was a match, we can dot-product the default value with the injected values as well and calculate: other_value + default_value - sum injected_i * default_value.
        let mut offset = state.id == PartyID::ID0;
        // Start the dot product with a random mask (for potential resharing later)
        let (mut dot, dot_b) = state.rngs.rand.random_biguint(F::MODULUS_BIT_SIZE as usize);
        dot ^= dot_b;
        let mut dot = F::BigInt::try_from(dot).expect("Works");
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

    fn network_round1<N: Rep3NetworkExt>(
        key_bits: &[Rep3RingShare<Bit>],
        to_compare: Vec<Rep3RingShare<u32>>,
        net0: &N,
        net1: &N,
        state0: &mut Rep3State,
    ) -> eyre::Result<NetworkRound1Result<F>> {
        let mut state1 = state0.fork(1).expect("Rep3 fork cannot fail");
        let (ohv_layer, bitinject) = std::thread::scope(|s| {
            let ohv_layer = s.spawn(|| crate::rep3::is_zero_many(to_compare, net0, state0));
            let bitinject = s.spawn(|| {
                crate::rep3::bit_inject_from_bits_to_field_many::<F, _>(key_bits, net1, &mut state1)
            });
            (
                ohv_layer.join().expect("can join"),
                bitinject.join().expect("can join"),
            )
        });

        let ohv_layer = ohv_layer?;
        let bitinject = bitinject?;
        Ok(NetworkRound1Result(ohv_layer, bitinject))
    }

    fn compute_merkle_path<N: Network>(
        &self,
        ohv: &[Rep3RingShare<Bit>],
        bitinject: Vec<Rep3PrimeFieldShare<F>>,
        net: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<Vec<ObliviousMerkleWitnessElement<F>>> {
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
        p: &ObliviousMerkleWitnessElement<F>,
        element: Rep3PrimeFieldShare<F>,
        net: &N,
        poseidon2: &Poseidon2<F, 2, 5>,
        poseidon2_precomputations: &mut Poseidon2Precomputations<Rep3PrimeFieldShare<F>>,
    ) -> eyre::Result<Rep3PrimeFieldShare<F>> {
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
    use itertools::izip;
    use mpc_core::protocols::{
        rep3::{self, Rep3State, conversion::A2BType},
        rep3_ring::{self, ring::ring_impl::RingElement},
    };
    use mpc_net::local::LocalNetwork;
    use std::str::FromStr;

    use crate::LinearScanObliviousMap;

    const DEFAULT_ROOT_BN254_FR: &str =
        "20656661903863297823367476705363945647184478890034741500819882513030138045548";

    #[test]
    fn defaults_correct() {
        let is_root = LinearScanObliviousMap::<ark_bn254::Fr>::new().root;
        let should_root = ark_bn254::Fr::from_str(DEFAULT_ROOT_BN254_FR).expect("works");
        assert_eq!(is_root, should_root);
    }

    #[test]
    fn read_empty_map() {
        let mut rng = rand::thread_rng();

        // generate a random key
        let key = RingElement(rand::random::<u32>());
        let [key_share0, key_share1, key_share2] =
            rep3_ring::share_ring_element_binary(key, &mut rng);

        // need two networks
        let [n0, n1, n2] = LocalNetwork::new_3_parties();
        let [n3, n4, n5] = LocalNetwork::new_3_parties();
        let random_default_value = ark_bn254::Fr::from(rand::random::<u128>());

        let [res0, res1, res2] = std::thread::scope(|s| {
            let res0 = s.spawn(|| {
                let map = LinearScanObliviousMap::<ark_bn254::Fr>::with_default_value(
                    random_default_value,
                );
                let mut state = Rep3State::new(&n0, A2BType::Direct).expect("works");
                map.read(key_share0, &n0, &n3, &mut state)
            });

            let res1 = s.spawn(|| {
                let map = LinearScanObliviousMap::<ark_bn254::Fr>::with_default_value(
                    random_default_value,
                );
                let mut state = Rep3State::new(&n1, A2BType::Direct).expect("works");
                map.read(key_share1, &n1, &n4, &mut state)
            });

            let res2 = s.spawn(|| {
                let map = LinearScanObliviousMap::<ark_bn254::Fr>::with_default_value(
                    random_default_value,
                );
                let mut state = Rep3State::new(&n2, A2BType::Direct).expect("works");
                map.read(key_share2, &n2, &n5, &mut state)
            });
            let res0 = res0.join().expect("can join").expect("did work");
            let res1 = res1.join().expect("can join").expect("did work");
            let res2 = res2.join().expect("can join").expect("did work");
            [res0, res1, res2]
        });

        let (res0, _) = res0;
        let (res1, _) = res1;
        let (res2, _) = res2;
        let result = res0 + res1 + res2;
        assert_eq!(result.a, random_default_value);
    }

    #[test]
    fn insert_then_read() {
        const TEST_SUITE: usize = 100;
        let mut rng = rand::thread_rng();

        // generate a random key/values
        let mut keys = Vec::with_capacity(TEST_SUITE);
        let mut values = Vec::with_capacity(TEST_SUITE);
        for _ in 0..TEST_SUITE {
            let mut key = rand::random::<RingElement<u32>>();
            while keys.contains(&key) {
                key = rand::random::<RingElement<u32>>();
            }
            keys.push(key);
            values.push(ark_bn254::Fr::from(rand::random::<u128>()));
        }

        let [key_share0, key_share1, key_share2] =
            rep3_ring::share_ring_elements_binary(&keys, &mut rng);
        let [value_share0, value_share1, value_share2] =
            rep3::share_field_elements(&values, &mut rng);

        // need two networks
        let [n0, n1, n2] = LocalNetwork::new_3_parties();
        let [n3, n4, n5] = LocalNetwork::new_3_parties();
        let random_default_value = ark_bn254::Fr::from(rand::random::<u128>());

        let [res0, res1, res2] = std::thread::scope(|s| {
            let res0 = s.spawn(|| {
                let mut map = LinearScanObliviousMap::<ark_bn254::Fr>::with_default_value(
                    random_default_value,
                );
                let mut state = Rep3State::new(&n0, A2BType::Direct).expect("works");
                let mut reads = Vec::with_capacity(TEST_SUITE);
                let mut defaults = Vec::with_capacity(TEST_SUITE);

                for (k, v) in izip!(key_share0, value_share0) {
                    // read first on key before insert
                    defaults.push(map.read(k, &n0, &n3, &mut state)?);
                    map.insert(k, v, &n0, &n3, &mut state)?;
                    reads.push(map.read(k, &n0, &n3, &mut state)?);
                }
                eyre::Ok((reads, defaults))
            });

            let res1 = s.spawn(|| {
                let mut map = LinearScanObliviousMap::<ark_bn254::Fr>::with_default_value(
                    random_default_value,
                );
                let mut state = Rep3State::new(&n1, A2BType::Direct).expect("works");
                let mut reads = Vec::with_capacity(TEST_SUITE);
                let mut defaults = Vec::with_capacity(TEST_SUITE);

                for (k, v) in izip!(key_share1, value_share1) {
                    // read first on key before insert
                    defaults.push(map.read(k, &n1, &n4, &mut state)?);
                    map.insert(k, v, &n1, &n4, &mut state)?;
                    reads.push(map.read(k, &n1, &n4, &mut state)?);
                }
                eyre::Ok((reads, defaults))
            });

            let res2 = s.spawn(|| {
                let mut map = LinearScanObliviousMap::<ark_bn254::Fr>::with_default_value(
                    random_default_value,
                );
                let mut state = Rep3State::new(&n2, A2BType::Direct).expect("works");
                let mut reads = Vec::with_capacity(TEST_SUITE);
                let mut defaults = Vec::with_capacity(TEST_SUITE);

                for (k, v) in izip!(key_share2, value_share2) {
                    // read first on key before insert
                    defaults.push(map.read(k, &n2, &n5, &mut state)?);
                    map.insert(k, v, &n2, &n5, &mut state)?;
                    reads.push(map.read(k, &n2, &n5, &mut state)?);
                }
                eyre::Ok((reads, defaults))
            });
            let res0 = res0.join().expect("can join").expect("did work");
            let res1 = res1.join().expect("can join").expect("did work");
            let res2 = res2.join().expect("can join").expect("did work");
            [res0, res1, res2]
        });

        let (reads0, defaults0) = res0;
        let (reads1, defaults1) = res1;
        let (reads2, defaults2) = res2;

        for (d0, d1, d2) in izip!(defaults0, defaults1, defaults2) {
            let (d0, _) = d0;
            let (d1, _) = d1;
            let (d2, _) = d2;
            assert_eq!((d0 + d1 + d2).a, random_default_value);
        }

        for (r0, r1, r2, should) in izip!(reads0, reads1, reads2, values) {
            let (r0, _) = r0;
            let (r1, _) = r1;
            let (r2, _) = r2;
            assert_eq!((r0 + r1 + r2).a, should);
        }
    }

    #[test]
    fn insert_update_then_read() {
        const TEST_SUITE: usize = 100;
        let mut rng = rand::thread_rng();

        // generate a random key/values
        let mut keys = Vec::with_capacity(TEST_SUITE);
        let mut values = Vec::with_capacity(TEST_SUITE);
        let mut updates = Vec::with_capacity(TEST_SUITE);
        for _ in 0..TEST_SUITE {
            let mut key = rand::random::<RingElement<u32>>();
            while keys.contains(&key) {
                key = rand::random::<RingElement<u32>>();
            }
            keys.push(key);
            values.push(ark_bn254::Fr::from(rand::random::<u128>()));
            updates.push(ark_bn254::Fr::from(rand::random::<u128>()));
        }

        let [key_share0, key_share1, key_share2] =
            rep3_ring::share_ring_elements_binary(&keys, &mut rng);
        let [value_share0, value_share1, value_share2] =
            rep3::share_field_elements(&values, &mut rng);
        let [update_share0, update_share1, update_share2] =
            rep3::share_field_elements(&updates, &mut rng);

        // need two networks
        let [n0, n1, n2] = LocalNetwork::new_3_parties();
        let [n3, n4, n5] = LocalNetwork::new_3_parties();
        let random_default_value = ark_bn254::Fr::from(rand::random::<u128>());

        let [res0, res1, res2] = std::thread::scope(|s| {
            let res0 = s.spawn(|| {
                let mut map = LinearScanObliviousMap::<ark_bn254::Fr>::with_default_value(
                    random_default_value,
                );
                let mut state = Rep3State::new(&n0, A2BType::Direct).expect("works");
                let mut reads = Vec::with_capacity(TEST_SUITE);

                for (k, v, u) in izip!(key_share0, value_share0, update_share0) {
                    map.insert(k, v, &n0, &n3, &mut state)?;
                    map.update(k, u, &n0, &n3, &mut state)?;
                    reads.push(map.read(k, &n0, &n3, &mut state)?);
                }
                eyre::Ok(reads)
            });

            let res1 = s.spawn(|| {
                let mut map = LinearScanObliviousMap::<ark_bn254::Fr>::with_default_value(
                    random_default_value,
                );
                let mut state = Rep3State::new(&n1, A2BType::Direct).expect("works");
                let mut reads = Vec::with_capacity(TEST_SUITE);

                for (k, v, u) in izip!(key_share1, value_share1, update_share1) {
                    map.insert(k, v, &n1, &n4, &mut state)?;
                    map.update(k, u, &n1, &n4, &mut state)?;
                    reads.push(map.read(k, &n1, &n4, &mut state)?);
                }
                eyre::Ok(reads)
            });

            let res2 = s.spawn(|| {
                let mut map = LinearScanObliviousMap::<ark_bn254::Fr>::with_default_value(
                    random_default_value,
                );
                let mut state = Rep3State::new(&n2, A2BType::Direct).expect("works");
                let mut reads = Vec::with_capacity(TEST_SUITE);
                for (k, v, u) in izip!(key_share2, value_share2, update_share2) {
                    map.insert(k, v, &n2, &n5, &mut state)?;
                    map.update(k, u, &n2, &n5, &mut state)?;
                    reads.push(map.read(k, &n2, &n5, &mut state)?);
                }
                eyre::Ok(reads)
            });
            let res0 = res0.join().expect("can join").expect("did work");
            let res1 = res1.join().expect("can join").expect("did work");
            let res2 = res2.join().expect("can join").expect("did work");
            [res0, res1, res2]
        });

        for (r0, r1, r2, should) in izip!(res0, res1, res2, updates) {
            let (r0, _) = r0;
            let (r1, _) = r1;
            let (r2, _) = r2;
            assert_eq!((r0 + r1 + r2).a, should);
        }
    }
}
