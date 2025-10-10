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
mod insert;
mod read;
pub mod rep3;
mod update;

pub const DELETED_LEAF_VALUE: u64 = 0xDEADBEEF;
pub const LINEAR_SCAN_TREE_DEPTH: usize = 32;

#[derive(Clone)]
pub struct ObliviousMembershipProof<F: PrimeField>(pub Vec<ObliviousMerkleWitnessElement<F>>);

struct NetworkRound1Result<F: PrimeField>(Vec<Rep3RingShare<Bit>>, Vec<Rep3PrimeFieldShare<F>>);

#[derive(Clone)]
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

    #[inline(always)]
    pub const fn depth(&self) -> usize {
        LINEAR_SCAN_TREE_DEPTH
    }

    pub fn verify_path<N: Network>(
        &self,
        element: Rep3PrimeFieldShare<F>,
        path: &ObliviousMembershipProof<F>,
        net: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<Rep3RingShare<Bit>> {
        let poseidon2 = Poseidon2::<F, 2, 5>::default();
        let mut poseidon2_precomputations =
            poseidon2.precompute_rep3(LINEAR_SCAN_TREE_DEPTH, net, state)?;

        let mut current_value = element;
        for p in path.0.iter() {
            current_value = Self::poseidon2_cmux(
                p,
                current_value,
                net,
                &poseidon2,
                &mut poseidon2_precomputations,
            )?;
        }
        // current_value == self.root
        let eq = arithmetic::eq_bit_public(current_value, self.root, net, state)?;

        // Translate to BitShare
        let eq = Rep3RingShare::<Bit>::new(eq.a.bit(0).into(), eq.b.bit(0).into());

        Ok(eq)
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
                let (read, path) = map.read(key_share0, &n0, &n3, &mut state)?;
                let check = map.verify_path(read, &path, &n0, &mut state)?;
                eyre::Ok((read, check))
            });

            let res1 = s.spawn(|| {
                let map = LinearScanObliviousMap::<ark_bn254::Fr>::with_default_value(
                    random_default_value,
                );
                let mut state = Rep3State::new(&n1, A2BType::Direct).expect("works");
                let (read, path) = map.read(key_share1, &n1, &n4, &mut state)?;
                let check = map.verify_path(read, &path, &n1, &mut state)?;
                eyre::Ok((read, check))
            });

            let res2 = s.spawn(|| {
                let map = LinearScanObliviousMap::<ark_bn254::Fr>::with_default_value(
                    random_default_value,
                );
                let mut state = Rep3State::new(&n2, A2BType::Direct).expect("works");
                let (read, path) = map.read(key_share2, &n2, &n5, &mut state)?;
                let check = map.verify_path(read, &path, &n2, &mut state)?;
                eyre::Ok((read, check))
            });
            let res0 = res0.join().expect("can join").expect("did work");
            let res1 = res1.join().expect("can join").expect("did work");
            let res2 = res2.join().expect("can join").expect("did work");
            [res0, res1, res2]
        });

        let (res0, check0) = res0;
        let (res1, check1) = res1;
        let (res2, check2) = res2;
        let result = res0 + res1 + res2;
        let check = check0 ^ check1 ^ check2;
        assert_eq!(result.a, random_default_value);
        assert!(check.a.convert().convert());
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
                let mut path_checks = Vec::with_capacity(TEST_SUITE * 3);

                for (k, v, u) in izip!(key_share0, value_share0, update_share0) {
                    // insert
                    let insert_path = map.insert(k, v, &n0, &n3, &mut state)?;
                    path_checks.push(map.verify_path(v, &insert_path, &n0, &mut state)?);

                    // update
                    let update_path = map.update(k, u, &n0, &n3, &mut state)?;
                    path_checks.push(map.verify_path(u, &update_path, &n0, &mut state)?);

                    // verify
                    let (read, read_path) = map.read(k, &n0, &n3, &mut state)?;
                    path_checks.push(map.verify_path(read, &read_path, &n0, &mut state)?);
                    reads.push(read);
                }
                eyre::Ok((reads, path_checks))
            });

            let res1 = s.spawn(|| {
                let mut map = LinearScanObliviousMap::<ark_bn254::Fr>::with_default_value(
                    random_default_value,
                );
                let mut state = Rep3State::new(&n1, A2BType::Direct).expect("works");
                let mut reads = Vec::with_capacity(TEST_SUITE);
                let mut path_checks = Vec::with_capacity(TEST_SUITE * 3);

                for (k, v, u) in izip!(key_share1, value_share1, update_share1) {
                    // insert
                    let insert_path = map.insert(k, v, &n1, &n4, &mut state)?;
                    path_checks.push(map.verify_path(v, &insert_path, &n1, &mut state)?);

                    // update
                    let update_path = map.update(k, u, &n1, &n4, &mut state)?;
                    path_checks.push(map.verify_path(u, &update_path, &n1, &mut state)?);

                    // verify
                    let (read, read_path) = map.read(k, &n1, &n4, &mut state)?;
                    path_checks.push(map.verify_path(read, &read_path, &n1, &mut state)?);
                    reads.push(read);
                }
                eyre::Ok((reads, path_checks))
            });

            let res2 = s.spawn(|| {
                let mut map = LinearScanObliviousMap::<ark_bn254::Fr>::with_default_value(
                    random_default_value,
                );
                let mut state = Rep3State::new(&n2, A2BType::Direct).expect("works");
                let mut reads = Vec::with_capacity(TEST_SUITE);
                let mut path_checks = Vec::with_capacity(TEST_SUITE * 3);

                for (k, v, u) in izip!(key_share2, value_share2, update_share2) {
                    // insert
                    let insert_path = map.insert(k, v, &n2, &n5, &mut state)?;
                    path_checks.push(map.verify_path(v, &insert_path, &n2, &mut state)?);

                    // update
                    let update_path = map.update(k, u, &n2, &n5, &mut state)?;
                    path_checks.push(map.verify_path(u, &update_path, &n2, &mut state)?);

                    // verify
                    let (read, read_path) = map.read(k, &n2, &n5, &mut state)?;
                    path_checks.push(map.verify_path(read, &read_path, &n2, &mut state)?);
                    reads.push(read);
                }
                eyre::Ok((reads, path_checks))
            });
            let res0 = res0.join().expect("can join").expect("did work");
            let res1 = res1.join().expect("can join").expect("did work");
            let res2 = res2.join().expect("can join").expect("did work");
            [res0, res1, res2]
        });

        let (reads0, checks0) = res0;
        let (reads1, checks1) = res1;
        let (reads2, checks2) = res2;

        for (r0, r1, r2, should) in izip!(reads0, reads1, reads2, updates) {
            assert_eq!((r0 + r1 + r2).a, should);
        }

        for (r0, r1, r2) in izip!(checks0, checks1, checks2) {
            assert!((r0 + r1 + r2).a.convert().convert());
        }
    }
}
