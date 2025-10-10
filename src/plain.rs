use ark_ff::{BigInteger256, PrimeField, UniformRand as _, Zero as _};
use mpc_core::{
    gadgets::poseidon2::Poseidon2,
    protocols::rep3_ring::{self, ring::ring_impl::RingElement},
};
use rand::{CryptoRng, Rng};

use crate::{LINEAR_SCAN_TREE_DEPTH, LinearScanObliviousMap};

#[derive(Debug, Default, Clone)]
struct Layer<F: PrimeField> {
    keys: Vec<u32>,
    values: Vec<F>,
}

impl<F: PrimeField> Layer<F> {
    pub fn len(&self) -> usize {
        self.keys.len()
    }
    #[expect(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }

    pub fn share_ring<R: Rng + CryptoRng>(&self, rng: &mut R) -> [crate::Layer<F>; 3] {
        debug_assert_eq!(self.keys.len(), self.values.len());
        let keys = self
            .keys
            .iter()
            .map(|k| RingElement::from(*k))
            .collect::<Vec<_>>();

        let [key_shares0, key_shares1, key_shares2] =
            rep3_ring::share_ring_elements_binary(&keys, rng);

        let [value_shares0, value_shares1, value_shares2] =
            crate::rep3::share_values_ring(&self.values, rng);

        let res0 = crate::Layer {
            keys: key_shares0,
            values: value_shares0,
        };
        let res1 = crate::Layer {
            keys: key_shares1,
            values: value_shares1,
        };
        let res2 = crate::Layer {
            keys: key_shares2,
            values: value_shares2,
        };

        [res0, res1, res2]
    }
}

pub struct LinearScanMap {
    layers: [Layer<ark_bn254::Fr>; LINEAR_SCAN_TREE_DEPTH],
    leaf_count: usize,
    total_count: usize,
    defaults: [BigInteger256; LINEAR_SCAN_TREE_DEPTH],
    root: ark_bn254::Fr,
}

impl LinearScanMap {
    pub fn unused_key<R: Rng>(&self, r: &mut R) -> u32 {
        let mut key = r.r#gen();
        while self.layers[0].keys.contains(&key) {
            key = rand::random();
        }
        key
    }

    pub fn used_key<R: Rng>(&self, r: &mut R) -> u32 {
        self.layers[0].keys[r.gen_range(0..self.leaf_count - 1)]
    }

    pub fn with_garbage_values<R: Rng>(mut keys: Vec<u32>, rng: &mut R) -> Self {
        let mut total_count = 0;
        let mut layers = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        for _ in 0..LINEAR_SCAN_TREE_DEPTH {
            let mut layer = Layer::default();

            let mut new_keys = Vec::with_capacity(keys.len());
            for key in keys.iter() {
                let new_key = *key >> 1;
                new_keys.push(new_key);
            }

            layer.values = (0..keys.len())
                .map(|_| ark_bn254::Fr::rand(rng))
                .collect::<Vec<_>>();
            layer.keys = keys;
            keys = new_keys;
            total_count += keys.len();
            layers.push(layer);
        }
        let mut default_value = ark_bn254::Fr::zero();
        let poseidon2 = Poseidon2::<ark_bn254::Fr, 2, 5>::default();
        let defaults = std::array::from_fn(|_| {
            let prev = default_value.into_bigint();
            default_value += poseidon2.permutation(&[default_value, default_value])[0];
            prev
        });
        Self {
            layers: layers.try_into().expect("works"),
            leaf_count: keys.len(),
            total_count,
            defaults,
            root: default_value,
        }
    }

    pub fn share<R: Rng + CryptoRng>(&self, rng: &mut R) -> [LinearScanObliviousMap; 3] {
        let mut total_count = 0;
        let leaf_count = self.layers[0].len();
        let mut layers0 = Vec::with_capacity(self.layers.len());
        let mut layers1 = Vec::with_capacity(self.layers.len());
        let mut layers2 = Vec::with_capacity(self.layers.len());
        for layer in self.layers.iter() {
            total_count += layer.len();
            let [layer0, layer1, layer2] = layer.share_ring(rng);
            layers0.push(layer0);
            layers1.push(layer1);
            layers2.push(layer2);
        }

        let res0 = LinearScanObliviousMap {
            layers: layers0.try_into().expect("works"),
            total_count,
            leaf_count,
            root: self.root,
            defaults: self.defaults,
        };
        let res1 = LinearScanObliviousMap {
            layers: layers1.try_into().expect("works"),
            total_count,
            leaf_count,
            root: self.root,
            defaults: self.defaults,
        };
        let res2 = LinearScanObliviousMap {
            layers: layers2.try_into().expect("works"),
            total_count,
            leaf_count,
            root: self.root,
            defaults: self.defaults,
        };
        [res0, res1, res2]
    }
}
