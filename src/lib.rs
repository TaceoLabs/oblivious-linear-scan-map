// #![deny(missing_docs)]
//! test
use ark_ff::{BigInteger256, One as _, PrimeField, Zero as _};
use ark_groth16::Proof;
use co_noir_to_r1cs::noir::r1cs;

use co_noir::{Bn254, Rep3AcvmType};
use co_noir_to_r1cs::trace::MpcTraceHasher as _;
use itertools::{Itertools as _, izip};
use mpc_core::{
    MpcState as _,
    gadgets::poseidon2::{Poseidon2, Poseidon2Precomputations},
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

use crate::{insert::InsertTail, update::UpdateTail};
mod groth16;
mod insert;
#[cfg(feature = "local")]
pub mod local;
mod mpc;
mod read;
mod update;

pub use groth16::Groth16Material;
pub use insert::ObliviousInsertRequest;
pub use insert::ObliviousInsertResult;
pub use read::ObliviousReadRequest;
pub use read::ObliviousReadResult;
pub use update::ObliviousUpdateRequest;

pub use mpc::Rep3BigIntShare;

/// The depth of the oblivious-linear-scan-tree.
pub const LINEAR_SCAN_TREE_DEPTH: usize = 32;
const INSERT_PROOF_INPUTS: usize = 68;
const READ_PROOF_INPUTS: usize = 65;

#[derive(Default, Debug, Clone)]
pub struct ObliviousLayer {
    keys: Vec<Rep3RingShare<u32>>,
    values: Vec<Rep3BigIntShare<ark_bn254::Fr>>,
}

struct PoseidonHashesWithTrace {
    new_root: Rep3PrimeFieldShare<ark_bn254::Fr>,
    layer_values: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
    proof_inputs: Vec<Rep3AcvmType<ark_bn254::Fr>>,
    traces: Vec<Vec<Rep3AcvmType<ark_bn254::Fr>>>,
}

struct PoseidonHashesWithTraceInput {
    new_value: Rep3PrimeFieldShare<ark_bn254::Fr>,
    old_value: Rep3PrimeFieldShare<ark_bn254::Fr>,
    bitinject: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
    merkle_witness: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
    randomness_index: Rep3PrimeFieldShare<ark_bn254::Fr>,
    randomness_commitment: Rep3PrimeFieldShare<ark_bn254::Fr>,
    precompute: Poseidon2Precomputations<Rep3PrimeFieldShare<ark_bn254::Fr>>,
}

struct PathAndWitness {
    path: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
    witness: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
}
impl ObliviousLayer {
    #[cfg(feature = "local")]
    pub fn new(keys: Vec<Rep3RingShare<u32>>, values: Vec<Rep3BigIntShare<ark_bn254::Fr>>) -> Self {
        Self { keys, values }
    }
}

pub struct LinearScanObliviousMap {
    layers: [ObliviousLayer; LINEAR_SCAN_TREE_DEPTH],
    leaf_count: usize,
    total_count: usize,
    defaults: [BigInteger256; LINEAR_SCAN_TREE_DEPTH],
    root: ark_bn254::Fr,
    read_groth16: Groth16Material,
    write_groth16: Groth16Material,
}

impl LinearScanObliviousMap {
    pub fn new(read_groth16: Groth16Material, write_groth16: Groth16Material) -> Self {
        Self::with_default_value(ark_bn254::Fr::zero(), read_groth16, write_groth16)
    }

    pub fn with_default_value(
        mut default_value: ark_bn254::Fr,
        read_groth16: Groth16Material,
        write_groth16: Groth16Material,
    ) -> Self {
        let poseidon2 = Poseidon2::<ark_bn254::Fr, 2, 5>::default();
        let defaults = std::array::from_fn(|_| {
            let prev = default_value.into_bigint();
            default_value += poseidon2.permutation(&[default_value, default_value])[0];
            prev
        });
        Self {
            layers: std::array::from_fn(|_| ObliviousLayer::default()),
            leaf_count: 0,
            total_count: 0,
            defaults,
            root: default_value,
            read_groth16,
            write_groth16,
        }
    }

    #[cfg(feature = "local")]
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
            layers,
            leaf_count,
            total_count,
            defaults,
            root,
            read_groth16,
            write_groth16,
        }
    }

    #[inline(always)]
    pub const fn depth(&self) -> usize {
        LINEAR_SCAN_TREE_DEPTH
    }

    #[expect(clippy::too_many_arguments)]
    pub fn oblivious_insert_or_update<N: Rep3NetworkExt>(
        &mut self,
        key: Rep3RingShare<u32>,
        insert_value: Rep3PrimeFieldShare<ark_bn254::Fr>,
        net0: &N,
        net1: &N,
        randomness_index: Rep3PrimeFieldShare<ark_bn254::Fr>,
        randomness_commitment: Rep3PrimeFieldShare<ark_bn254::Fr>,
        state0: &mut Rep3State,
    ) -> eyre::Result<()> {
        // we need to check if the value is present in the leaf layer.
        // we do that by computing the ohv of the path and xor the leaf values.
        let mut state1 = state0.fork(1).expect("cant fail for rep3");

        let ((present_bit, path_ohv), (merkle_witness, bitinject)) = Self::join(
            || self.is_value_in_leaves(key, net0, state0),
            || {
                let merkle_witness = self.read_merkle_witness(key, net1, &mut state1)?;
                let bitinject = Self::key_decompose(key, net1, &mut state1)?;
                Ok((merkle_witness, bitinject))
            },
        )?;
        if present_bit {
            // is present - need to update
            let update_tail = UpdateTail {
                update_value: insert_value,
                path_ohv,
                merkle_witness,
                bitinject,
                randomness_index,
                randomness_commitment,
            };
            self.update_tail(update_tail, net0, net1, state0, &mut state1)?;
        } else {
            // not present - need to insert
            let insert_tail = InsertTail {
                key,
                insert_value,
                path_ohv,
                merkle_witness,
                bitinject,
                randomness_index,
                randomness_commitment,
            };
            self.insert_tail(insert_tail, net0, net1, state0)?;
        }
        Ok(())
    }

    fn join<F0, T0, F1, T1>(f0: F0, f1: F1) -> eyre::Result<(T0, T1)>
    where
        F0: FnOnce() -> eyre::Result<T0> + Send,
        T0: Send,
        F1: FnOnce() -> eyre::Result<T1> + Send,
        T1: Send,
    {
        std::thread::scope(|s| {
            let s0 = s.spawn(f1);
            eyre::Ok((f0()?, s0.join().expect("can join")?))
        })
    }

    fn push_new_values(&mut self, values: Vec<Rep3BigUintShare<ark_bn254::Fr>>) {
        for (layer, new_value) in izip!(self.layers.iter_mut(), values) {
            layer.values.push(new_value.try_into().expect("Works"));
        }
    }

    fn is_value_in_leaves<N: Rep3NetworkExt>(
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

    #[instrument(level = "debug", skip_all)]
    fn key_decompose<N: Rep3NetworkExt>(
        key: Rep3RingShare<u32>,
        net: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>> {
        let key_bits = (0..32).map(|shift| (key >> shift).get_bit(0)).collect_vec();
        // also do the bitinject
        crate::mpc::bit_inject_from_bits_to_field_many(&key_bits, net, state)
    }

    /// Computes a co-SNARK with the provided [`Groth16Material`]. The traces for the poseidon hashes
    /// need to be computed in advance.
    fn co_snark<N: Rep3NetworkExt>(
        inputs: Vec<Rep3AcvmType<ark_bn254::Fr>>,
        traces: Vec<Vec<Rep3AcvmType<ark_bn254::Fr>>>,
        groth16_material: &Groth16Material,
        net0: &N,
        net1: &N,
        state0: &mut Rep3State,
    ) -> eyre::Result<(Proof<Bn254>, Vec<ark_bn254::Fr>)> {
        let Groth16Material {
            proof_schema,
            cs,
            pk,
        } = groth16_material;
        let r1cs = r1cs::trace_to_r1cs_witness(inputs, traces, proof_schema, net0, net1, state0)?;
        let witness = r1cs::r1cs_witness_to_cogroth16(proof_schema, r1cs, state0.id);
        let (proof, public_inputs) = r1cs::prove(cs, pk, witness, net0, net1)?;
        tracing::trace!("< groth16 read proof");
        Ok((proof, public_inputs))
    }

    /// Computes the poseidon hashes for inserts/updates.
    ///
    /// In contrast to read, we can't compute all hashes in parallel.
    /// This method recomputes the hashes for the old root and the new root.
    ///
    /// The very first round also computes the hashes for the commitment to safe a Poseidon2-depth.
    #[instrument(level = "debug", skip_all)]
    fn poseidon_hashes_with_write_traces<N: Rep3NetworkExt>(
        input: PoseidonHashesWithTraceInput,
        net: &N,
    ) -> eyre::Result<PoseidonHashesWithTrace> {
        let PoseidonHashesWithTraceInput {
            new_value,
            old_value,
            bitinject,
            merkle_witness,
            randomness_index,
            randomness_commitment,
            mut precompute,
        } = input;
        let mut proof_inputs = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        let mut layer_values = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        let mut traces_new_root = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        let mut traces_old_root = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH);
        layer_values.push(new_value);

        let mut current_value_new = new_value;
        let mut current_value_old = old_value;

        // in the first run we also do the poseidon hashes for the two commitments

        // Calculate the commitment to the index
        let mut index = Rep3PrimeFieldShare::zero();
        for p in bitinject.iter().rev() {
            index += index;
            index += p;
        }

        let [left_new, right_new, left_old, right_old] = prep_poseidon(
            merkle_witness[0],
            current_value_new,
            current_value_old,
            bitinject[0],
            net,
        )?;
        let ins = [
            left_new,
            right_new,
            left_old,
            right_old,
            index,
            randomness_index,
            new_value,
            randomness_commitment,
        ];
        let poseidon2 = Poseidon2::<ark_bn254::Fr, 2, 5>::default();
        let (hashes, traces) =
            poseidon2.hash_rep3_generate_noir_trace_many::<_, 4, 8>(ins, &mut precompute, net)?;
        let [new_trace, old_trace, index_trace, value_trace] = traces;
        proof_inputs.push(Rep3AcvmType::from(merkle_witness[0]));
        layer_values.push(hashes[0]);
        traces_new_root.push(new_trace);
        traces_old_root.push(old_trace);
        current_value_new = hashes[0];
        current_value_old = hashes[1];

        // Hashes for the rest of the tree.
        for (other, position) in izip!(merkle_witness, bitinject.clone()).skip(1) {
            let input = prep_poseidon(other, current_value_new, current_value_old, position, net)?;

            let (hashes, trace) = poseidon2.hash_rep3_generate_noir_trace_many::<_, 2, 4>(
                input,
                &mut precompute,
                net,
            )?;
            let [new_trace, old_trace] = trace;
            proof_inputs.push(Rep3AcvmType::from(other));
            layer_values.push(hashes[0]);
            traces_new_root.push(new_trace);
            traces_old_root.push(old_trace);
            current_value_new = hashes[0];
            current_value_old = hashes[1];
        }
        proof_inputs.push(Rep3AcvmType::from(randomness_index));
        proof_inputs.push(Rep3AcvmType::from(randomness_commitment));
        traces_old_root.extend(traces_new_root);
        traces_old_root.push(index_trace);
        traces_old_root.push(value_trace);
        Ok(PoseidonHashesWithTrace {
            new_root: current_value_new,
            layer_values,
            proof_inputs,
            traces: traces_old_root,
        })
    }

    fn promote_default_value<N: Rep3NetworkExt>(
        &self,
        net: &N,
    ) -> Rep3PrimeFieldShare<ark_bn254::Fr> {
        let party_id = net.id().try_into().expect("works for rep3 network");

        mpc_core::protocols::rep3::arithmetic::promote_to_trivial_share(
            party_id,
            self.defaults[0].into(),
        )
    }

    fn find_witness(&self, mut needle: Rep3RingShare<u32>) -> Vec<Rep3RingShare<u32>> {
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

    fn find_path(&self, mut needle: Rep3RingShare<u32>) -> Vec<Rep3RingShare<u32>> {
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

    fn read_merkle_path<N: Rep3NetworkExt>(
        &self,
        key: Rep3RingShare<u32>,
        net: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>> {
        let path_ohv = crate::mpc::is_zero_many(self.find_path(key), net, state)?;
        self.read_from_layers_with_ohv(&path_ohv, net, state)
    }

    fn read_merkle_witness<N: Rep3NetworkExt>(
        &self,
        key: Rep3RingShare<u32>,
        net: &N,
        state: &mut Rep3State,
    ) -> eyre::Result<Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>> {
        let path_ohv = crate::mpc::is_zero_many(self.find_witness(key), net, state)?;
        self.read_from_layers_with_ohv(&path_ohv, net, state)
    }

    #[instrument(level = "debug", skip_all)]
    fn read_path_and_witness<N: Rep3NetworkExt>(
        &self,
        key: Rep3RingShare<u32>,
        net0: &N,
        net1: &N,
        state0: &mut Rep3State,
        state1: &mut Rep3State,
    ) -> eyre::Result<PathAndWitness> {
        tracing::trace!("> reading path and witness...");
        let (path, witness) = Self::join(
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

    fn read_from_leaf_layer<N: Rep3NetworkExt>(
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

fn oblivious_switch(
    lhs: Rep3PrimeFieldShare<ark_bn254::Fr>,
    rhs: Rep3PrimeFieldShare<ark_bn254::Fr>,
    selector: Rep3PrimeFieldShare<ark_bn254::Fr>,
) -> (ark_bn254::Fr, ark_bn254::Fr) {
    let left_a = (lhs - rhs) * selector + rhs.a;
    let right_a = (rhs - lhs) * selector + lhs.a;
    (left_a, right_a)
}

/// Prepares the inputs for the two hashes used to compute the root for a specific layer.
/// Depending on position we need to decide whether we need to put the values as left or right input to Poseidon2.
///
/// This method performs this switch.
fn prep_poseidon<N: Rep3NetworkExt>(
    other: Rep3PrimeFieldShare<ark_bn254::Fr>,
    current_value_new: Rep3PrimeFieldShare<ark_bn254::Fr>,
    current_value_old: Rep3PrimeFieldShare<ark_bn254::Fr>,
    position: Rep3PrimeFieldShare<ark_bn254::Fr>,
    net: &N,
) -> eyre::Result<[Rep3PrimeFieldShare<ark_bn254::Fr>; 4]> {
    let (new_left, new_right) = oblivious_switch(other, current_value_new, position);
    let (old_left, old_right) = oblivious_switch(other, current_value_old, position);
    let bs = net.reshare_many(&[new_left, new_right, old_left, old_right])?;
    let left_new = Rep3PrimeFieldShare::new(new_left, bs[0]);
    let right_new = Rep3PrimeFieldShare::new(new_right, bs[1]);
    let left_old = Rep3PrimeFieldShare::new(old_left, bs[2]);
    let right_old = Rep3PrimeFieldShare::new(old_right, bs[3]);
    Ok([left_new, right_new, left_old, right_old])
}
#[cfg(test)]
mod tests {
    use co_noir_to_r1cs::noir::{r1cs, ultrahonk};
    use std::str::FromStr;

    use crate::{LinearScanObliviousMap, groth16::Groth16Material};

    const DEFAULT_ROOT_BN254_FR: &str =
        "20656661903863297823367476705363945647184478890034741500819882513030138045548";

    pub fn groth16_material() -> eyre::Result<(Groth16Material, Groth16Material)> {
        let root = std::env!("CARGO_MANIFEST_DIR");
        let read_program = ultrahonk::get_program_artifact(format!(
            "{root}/noir/compiled_circuits/oblivious_map_read.json"
        ))?;
        let write_program = ultrahonk::get_program_artifact(format!(
            "{root}/noir/compiled_circuits/oblivious_map_write.json"
        ))?;
        let (proof_schema_read, pk_read, cs_read) =
            r1cs::setup_r1cs(read_program, &mut rand::thread_rng())?;
        let (proof_schema_write, pk_write, cs_write) =
            r1cs::setup_r1cs(write_program, &mut rand::thread_rng())?;
        Ok((
            Groth16Material::new(proof_schema_read, cs_read, pk_read),
            Groth16Material::new(proof_schema_write, cs_write, pk_write),
        ))
    }

    #[test]
    fn defaults_correct() -> eyre::Result<()> {
        let (read_groth16, write_groth16) = groth16_material()?;
        let is_root = LinearScanObliviousMap::new(read_groth16, write_groth16).root;
        let should_root = ark_bn254::Fr::from_str(DEFAULT_ROOT_BN254_FR).expect("works");
        assert_eq!(is_root, should_root);
        Ok(())
    }
}
