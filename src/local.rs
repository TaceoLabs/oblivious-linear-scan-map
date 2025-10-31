use ark_ff::{BigInteger256, PrimeField, UniformRand as _, Zero as _};
use co_noir_to_r1cs::noir::{r1cs, ultrahonk};
use mpc_core::{
    gadgets::poseidon2::Poseidon2,
    protocols::rep3_ring::{self, Rep3RingShare, ring::ring_impl::RingElement},
};
use rand::{CryptoRng, Rng};

use crate::{
    Groth16Material, LINEAR_SCAN_TREE_DEPTH, LinearScanObliviousMap, ObliviousLayer,
    Rep3BigIntShare, base::MapBase,
};

impl ObliviousLayer {
    pub fn new(keys: Vec<Rep3RingShare<u32>>, values: Vec<Rep3BigIntShare<ark_bn254::Fr>>) -> Self {
        Self { keys, values }
    }
}

impl LinearScanObliviousMap {
    pub fn from_shared_values(
        layers: [ObliviousLayer; LINEAR_SCAN_TREE_DEPTH],
        leaf_count: usize,
        total_count: usize,
        defaults: [BigInteger256; LINEAR_SCAN_TREE_DEPTH],
        root: ark_bn254::Fr,
        read_groth16: Groth16Material,
        write_groth16: Groth16Material,
    ) -> Self {
        Self {
            inner: MapBase::from_shared_values(layers, leaf_count, total_count, defaults, root),
            read_groth16,
            write_groth16,
        }
    }
}

pub fn share_values_ring<F: PrimeField, R: Rng + CryptoRng>(
    values: &[F],
    rng: &mut R,
) -> [Vec<Rep3BigIntShare<F>>; 3] {
    let mut shares1 = Vec::with_capacity(values.len());
    let mut shares2 = Vec::with_capacity(values.len());
    let mut shares3 = Vec::with_capacity(values.len());
    for val in values {
        let [share1, share2, share3] = mpc_core::protocols::rep3::share_biguint(*val, rng);
        shares1.push(share1.try_into().expect("Works"));
        shares2.push(share2.try_into().expect("Works"));
        shares3.push(share3.try_into().expect("Works"));
    }
    [shares1, shares2, shares3]
}

impl MapBase {
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
}

#[derive(Debug, Default, Clone)]
struct Layer {
    keys: Vec<u32>,
    values: Vec<ark_bn254::Fr>,
}

impl Layer {
    pub fn len(&self) -> usize {
        self.keys.len()
    }
    #[expect(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }

    pub fn share_ring<R: Rng + CryptoRng>(&self, rng: &mut R) -> [ObliviousLayer; 3] {
        debug_assert_eq!(self.keys.len(), self.values.len());
        let keys = self
            .keys
            .iter()
            .map(|k| RingElement::from(*k))
            .collect::<Vec<_>>();

        let [key_shares0, key_shares1, key_shares2] =
            rep3_ring::share_ring_elements_binary(&keys, rng);

        let [value_shares0, value_shares1, value_shares2] = share_values_ring(&self.values, rng);

        let res0 = ObliviousLayer::new(key_shares0, value_shares0);
        let res1 = ObliviousLayer::new(key_shares1, value_shares1);
        let res2 = ObliviousLayer::new(key_shares2, value_shares2);

        [res0, res1, res2]
    }
}

pub struct LinearScanMap {
    layers: [Layer; LINEAR_SCAN_TREE_DEPTH],
    leaf_count: usize,
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
        let mut layers = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        let mut current_size = keys.len();
        for lvl in 0..LINEAR_SCAN_TREE_DEPTH {
            let mut layer = Layer::default();

            let mut new_keys = Vec::with_capacity(keys.len());
            for key in keys.iter() {
                let new_key = *key >> 1;
                new_keys.push(new_key);
            }

            layer.values = (0..current_size)
                .map(|_| ark_bn254::Fr::rand(rng))
                .collect::<Vec<_>>();
            if lvl != 0 && 1 << (32 - lvl) < current_size {
                current_size = 1 << (32 - lvl);
            }
            layer.keys = keys;
            keys = new_keys;
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
            defaults,
            root: default_value,
        }
    }

    pub fn share<R: Rng + CryptoRng>(
        &self,
        rng: &mut R,
    ) -> eyre::Result<[LinearScanObliviousMap; 3]> {
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
        let root = std::env!("CARGO_MANIFEST_DIR");
        let read_program = ultrahonk::get_program_artifact(format!(
            "{root}/noir/compiled_circuits/oblivious_map_read.json"
        ))?;
        let (proof_schema, pk, cs) = r1cs::setup_r1cs(read_program, &mut rand::thread_rng())?;
        let read_material = Groth16Material::new(proof_schema, cs, pk.clone());

        let write_program = ultrahonk::get_program_artifact(format!(
            "{root}/noir/compiled_circuits/oblivious_map_write.json"
        ))?;
        let (proof_schema, pk, cs) = r1cs::setup_r1cs(write_program, &mut rand::thread_rng())?;
        let write_material = Groth16Material::new(proof_schema, cs, pk.clone());

        let res0 = LinearScanObliviousMap::from_shared_values(
            layers0.try_into().expect("works"),
            leaf_count,
            total_count,
            self.defaults,
            self.root,
            read_material.clone(),
            write_material.clone(),
        );
        let res1 = LinearScanObliviousMap::from_shared_values(
            layers1.try_into().expect("works"),
            leaf_count,
            total_count,
            self.defaults,
            self.root,
            read_material.clone(),
            write_material.clone(),
        );
        let res2 = LinearScanObliviousMap::from_shared_values(
            layers2.try_into().expect("works"),
            leaf_count,
            total_count,
            self.defaults,
            self.root,
            read_material.clone(),
            write_material.clone(),
        );
        Ok([res0, res1, res2])
    }
}
