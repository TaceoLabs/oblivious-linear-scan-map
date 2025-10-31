use ark_ff::{BigInteger256, One as _, PrimeField};

use ark_serialize::CanonicalDeserialize;
use ark_serialize::CanonicalSerialize;
use co_noir::Rep3AcvmType;
use itertools::{Itertools as _, izip};
use mpc_core::{
    gadgets::poseidon2::Poseidon2Precomputations,
    protocols::{
        rep3::{
            Rep3BigUintShare, Rep3PrimeFieldShare, Rep3State, conversion, id::PartyID,
            network::Rep3NetworkExt,
        },
        rep3_ring::{
            Rep3RingShare,
            ring::{bit::Bit, ring_impl::RingElement},
        },
    },
};
use tracing::instrument;

use crate::LINEAR_SCAN_TREE_DEPTH;
use crate::ObliviousLayer;
use crate::Rep3BigIntShare;

pub(crate) struct PoseidonHashesWithTrace {
    pub(crate) new_root: Rep3PrimeFieldShare<ark_bn254::Fr>,
    pub(crate) layer_values: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
    pub(crate) proof_inputs: Vec<Rep3AcvmType<ark_bn254::Fr>>,
    pub(crate) traces: Vec<Vec<Rep3AcvmType<ark_bn254::Fr>>>,
}

pub(crate) struct PoseidonHashesWithTraceInput {
    pub(crate) new_value: Rep3PrimeFieldShare<ark_bn254::Fr>,
    pub(crate) old_value: Rep3PrimeFieldShare<ark_bn254::Fr>,
    pub(crate) bitinject: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
    pub(crate) merkle_witness: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
    pub(crate) randomness_index: Rep3PrimeFieldShare<ark_bn254::Fr>,
    pub(crate) randomness_commitment: Rep3PrimeFieldShare<ark_bn254::Fr>,
    pub(crate) precompute: Poseidon2Precomputations<Rep3PrimeFieldShare<ark_bn254::Fr>>,
}

pub(crate) struct PathAndWitness {
    pub(crate) path: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
    pub(crate) witness: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub(crate) struct MapBase {
    pub(crate) layers: [ObliviousLayer; LINEAR_SCAN_TREE_DEPTH],
    pub(crate) leaf_count: usize,
    pub(crate) total_count: usize,
    pub(crate) defaults: [BigInteger256; LINEAR_SCAN_TREE_DEPTH],
    pub(crate) root: ark_bn254::Fr,
}

impl MapBase {
    pub(super) fn new(
        defaults: [BigInteger256; LINEAR_SCAN_TREE_DEPTH],
        root: ark_bn254::Fr,
    ) -> Self {
        Self {
            layers: std::array::from_fn(|_| ObliviousLayer::default()),
            leaf_count: 0,
            total_count: 0,
            defaults,
            root,
        }
    }

    #[cfg(feature = "local")]
    pub fn from_shared_values(
        layers: [ObliviousLayer; LINEAR_SCAN_TREE_DEPTH],
        leaf_count: usize,
        total_count: usize,
        defaults: [BigInteger256; LINEAR_SCAN_TREE_DEPTH],
        root: ark_bn254::Fr,
    ) -> Self {
        Self {
            layers,
            leaf_count,
            total_count,
            defaults,
            root,
        }
    }

    #[instrument(level = "debug", skip_all)]
    pub(crate) fn key_decompose<N: Rep3NetworkExt>(
        key: Rep3RingShare<u32>,
        net: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>> {
        // we only need the 32 key-bits
        let key_bits = (0..32).map(|shift| (key >> shift).get_bit(0)).collect_vec();
        // also do the bitinject
        crate::mpc::bit_inject_from_bits_to_field_many(&key_bits, net, state)
    }

    pub(crate) fn push_new_values(&mut self, values: Vec<Rep3BigUintShare<ark_bn254::Fr>>) {
        for (layer, new_value) in izip!(self.layers.iter_mut(), values) {
            layer.values.push(new_value.try_into().expect("Works"));
        }
    }

    pub(crate) fn is_value_in_leaves<N: Rep3NetworkExt>(
        &self,
        key: Rep3RingShare<u32>,
        net: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<(bool, Vec<Rep3RingShare<Bit>>)> {
        let path_ohv = crate::mpc::is_zero_many(self.find_path(key), net, state)?;
        let present_bit = path_ohv[..self.layers[0].values.len()]
            .iter()
            .fold(Rep3RingShare::zero_share(), |acc, x| acc ^ *x);
        // open the present bit
        let other = net.reshare(present_bit.b)?;
        let present_bit = other + present_bit.a + present_bit.b;
        Ok((present_bit.convert().convert(), path_ohv))
    }

    pub(crate) fn promote_default_value<N: Rep3NetworkExt>(
        &self,
        net: &N,
    ) -> Rep3PrimeFieldShare<ark_bn254::Fr> {
        let party_id = net.id().try_into().expect("works for rep3 network");

        mpc_core::protocols::rep3::arithmetic::promote_to_trivial_share(
            party_id,
            self.defaults[0].into(),
        )
    }

    pub(crate) fn find_witness(&self, mut needle: Rep3RingShare<u32>) -> Vec<Rep3RingShare<u32>> {
        // To find the witness
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

    pub(crate) fn find_path(&self, mut needle: Rep3RingShare<u32>) -> Vec<Rep3RingShare<u32>> {
        // To find the path
        let mut result = Vec::with_capacity(self.total_count);
        for layer in self.layers.iter() {
            for hay in layer.keys.iter() {
                result.push(hay ^ &needle);
            }
            needle.a >>= 1;
            needle.b >>= 1;
        }
        result
    }

    pub(crate) fn read_merkle_path<N: Rep3NetworkExt>(
        &self,
        key: Rep3RingShare<u32>,
        net: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>> {
        let path_ohv = crate::mpc::is_zero_many(self.find_path(key), net, state)?;
        self.read_from_layers_with_ohv(&path_ohv, net, state)
    }

    pub(crate) fn read_merkle_witness<N: Rep3NetworkExt>(
        &self,
        key: Rep3RingShare<u32>,
        net: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>> {
        let path_ohv = crate::mpc::is_zero_many(self.find_witness(key), net, state)?;
        self.read_from_layers_with_ohv(&path_ohv, net, state)
    }

    #[instrument(level = "debug", skip_all)]
    pub(crate) fn read_path_and_witness<N: Rep3NetworkExt>(
        &self,
        key: Rep3RingShare<u32>,
        net0: &N,
        net1: &N,
        state0: &mut Rep3State,
        state1: &mut Rep3State,
    ) -> eyre::Result<PathAndWitness> {
        tracing::trace!("> reading path and witness...");
        let (path, witness) = crate::join(
            || self.read_merkle_path(key, net0, state0),
            || self.read_merkle_witness(key, net1, state1),
        )?;
        tracing::trace!("< reading path and witness...");
        Ok(PathAndWitness { path, witness })
    }

    fn read_from_layers_with_ohv<N: Rep3NetworkExt>(
        &self,
        ohv: &[Rep3RingShare<Bit>],
        net: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>> {
        let mut dots_a = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        let mut start = 0;
        for (layer, default) in izip!(self.layers.iter(), self.defaults.into_iter()) {
            let end = start + layer.keys.len();
            let dot = Self::dot(&ohv[start..end], &layer.values, default, state);
            start = end;
            dots_a.push(dot);
        }
        let dots_b = net.reshare_many(&dots_a)?;
        let dots = izip!(dots_a, dots_b)
            .map(|(a, b)| Rep3BigUintShare::<ark_bn254::Fr>::new(a.into(), b.into()))
            .collect_vec();

        conversion::b2a_many(&dots, net, state)
    }

    pub(crate) fn read_from_leaf_layer<N: Rep3NetworkExt>(
        &self,
        ohv: &[Rep3RingShare<Bit>],
        net: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<Rep3PrimeFieldShare<ark_bn254::Fr>> {
        let leaf_layer = &self.layers[0];

        let dot_a = Self::dot(
            &ohv[..leaf_layer.keys.len()],
            &leaf_layer.values,
            self.defaults[0],
            state,
        );
        let dot_b = net.reshare(dot_a)?;
        let dot = Rep3BigUintShare::<ark_bn254::Fr>::new(dot_a.into(), dot_b.into());

        conversion::b2a(&dot, net, state)
    }

    fn dot(
        ohv: &[Rep3RingShare<Bit>],
        other: &[Rep3BigIntShare<ark_bn254::Fr>],
        default: BigInteger256,
        state: &mut Rep3State,
    ) -> BigInteger256 {
        debug_assert_eq!(
            ohv.len(),
            other.len(),
            "The length of the two vectors must be equal"
        );

        // Set the default value:
        // Assuming only one element was a match, we can dot-product the default value with the injected values as well and calculate: other_value + default_value - sum injected_i * default_value.
        let mut offset = state.id == PartyID::ID0;
        // Start the dot product with a random mask (for potential re-sharing later)
        let (mut dot, dot_b) = state
            .rngs
            .rand
            .random_biguint(ark_bn254::Fr::MODULUS_BIT_SIZE as usize);
        dot ^= dot_b;
        let mut dot = BigInteger256::try_from(dot).expect("Works");
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
}
