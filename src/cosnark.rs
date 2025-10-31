use ark_ff::Zero as _;

use ark_groth16::Proof;
use co_noir::{Bn254, Rep3AcvmType};
use co_noir_to_r1cs::{noir::r1cs, trace::MpcTraceHasher as _};
use itertools::{Itertools as _, izip};
use mpc_core::{
    gadgets::poseidon2::Poseidon2,
    protocols::rep3::{self, Rep3PrimeFieldShare, Rep3State, network::Rep3NetworkExt},
};

use co_circom::{ConstraintMatrices, ProvingKey};
use co_noir_to_r1cs::r1cs::noir_proof_schema::NoirProofScheme;
use tracing::instrument;

use crate::{
    LINEAR_SCAN_TREE_DEPTH, READ_PROOF_INPUTS,
    base::{PathAndWitness, PoseidonHashesWithTrace, PoseidonHashesWithTraceInput},
};

#[derive(Clone)]
pub struct Groth16Material {
    pub(crate) proof_schema: NoirProofScheme<ark_bn254::Fr>,
    pub(crate) cs: ConstraintMatrices<ark_bn254::Fr>,
    pub(crate) pk: ProvingKey<Bn254>,
}

pub(crate) struct ReadWithTrace {
    pub(crate) read_value: Rep3PrimeFieldShare<ark_bn254::Fr>,
    pub(crate) inputs: Vec<Rep3AcvmType<ark_bn254::Fr>>,
    pub(crate) traces: Vec<Vec<Rep3AcvmType<ark_bn254::Fr>>>,
}

/// Helper struct only used to group the inputs to the proof and traces together.
/// We just want to make clippy happy.
pub(crate) struct InsertWithTrace {
    pub(crate) inputs: Vec<Rep3AcvmType<ark_bn254::Fr>>,
    pub(crate) traces: Vec<Vec<Rep3AcvmType<ark_bn254::Fr>>>,
}

impl Groth16Material {
    /// Creates the Groth16 material by providing the actual values.
    pub fn new(
        proof_schema: NoirProofScheme<ark_bn254::Fr>,
        cs: ConstraintMatrices<ark_bn254::Fr>,
        pk: ProvingKey<Bn254>,
    ) -> Self {
        Self {
            proof_schema,
            cs,
            pk,
        }
    }
}

/// Computes a co-SNARK with the provided [`Groth16Material`]. The traces for the poseidon hashes
/// need to be computed in advance.
///
/// Uses co-ACVM for the witness extension and then transforms the noir witness
/// into R1CS. Then uses co-Groth16 to prove the statement.
pub(crate) fn noir_groth16<N: Rep3NetworkExt>(
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

/// Builds the execution traces for the read co-SNARK. We provide the path and the witness elements both, so we can do all
/// Poseidons at the same time. This reduces the multiplicative depth only one Poseidon2.
///
/// Additionally, we also produce the commitment to the key at the same time.
///
/// This method returns
/// - the read value
/// - the inputs for the coSNARK
/// - the execution traces for all hashes to not compute them in co-ACVM.
#[instrument(level = "debug", skip_all)]
pub(crate) fn build_read_execution_trace<N: Rep3NetworkExt>(
    path_and_witness: PathAndWitness,
    positions: Vec<Rep3PrimeFieldShare<ark_bn254::Fr>>,
    randomness_commitment: Rep3PrimeFieldShare<ark_bn254::Fr>,
    net0: &N,
    net1: &N,
    state0: &mut Rep3State,
    state1: &mut Rep3State,
) -> eyre::Result<ReadWithTrace> {
    let PathAndWitness { path, witness } = path_and_witness;

    let mut proof_inputs = Vec::with_capacity(READ_PROOF_INPUTS);
    let read_value = path[0];
    // start building the proof inputs
    proof_inputs.push(read_value.into());
    for p in positions.clone().into_iter() {
        proof_inputs.push(p.into());
    }

    let hasher = Poseidon2::<ark_bn254::Fr, 2, 5>::default();
    let network1_span = tracing::debug_span!("build_read_trace::network1");
    let (mut pre_computations, switches) = network1_span.in_scope(|| {
        crate::join(
            || hasher.precompute_rep3(LINEAR_SCAN_TREE_DEPTH + 1, net0, state0),
            || {
                // we compute all switches at the same time
                // needed to determine if values are the left/right input to
                // Poseidon2
                tracing::trace!("computing switches...");
                let switches = izip!(path.iter(), witness.iter())
                    .map(|(p, w)| w - p)
                    .collect_vec();
                rep3::arithmetic::mul_vec(&positions, &switches, net1, state1)
            },
        )
    })?;

    tracing::trace!("doing oblivious switches...");
    let mut ins = Vec::with_capacity(LINEAR_SCAN_TREE_DEPTH * 2);
    for (p, w, mul) in izip!(path, witness, switches) {
        proof_inputs.push(w.into());
        let hash_left = mul + p;
        let hash_right = w - mul;
        ins.push(hash_left);
        ins.push(hash_right);
    }
    // Calculate the commitment to the index
    let mut index = Rep3PrimeFieldShare::zero();
    for p in positions.iter().rev() {
        index += index;
        index += p;
    }
    // the input for the commitment
    ins.push(index);
    ins.push(randomness_commitment);
    proof_inputs.push(randomness_commitment.into());

    // Compute the traces
    let noir_trace_span = tracing::debug_span!("build_read_trace::noir_traces");
    let (_, traces) = noir_trace_span.in_scope(|| {
        tracing::debug!("generating poseidon traces...");
        hasher.hash_rep3_generate_noir_trace_many::<_, 33, 66>(
            ins.try_into().expect("works"),
            &mut pre_computations,
            net0,
        )
    })?;
    Ok(ReadWithTrace {
        read_value,
        inputs: proof_inputs,
        traces: traces.to_vec(),
    })
}

/// Computes the poseidon hashes for inserts/updates.
///
/// In contrast to read, we can't compute all hashes in parallel.
/// This method recomputes the hashes for the old root and the new root.
///
/// The very first round also computes the hashes for the commitment to safe a Poseidon2-depth.
#[instrument(level = "debug", skip_all)]
pub(crate) fn poseidon_hashes_with_write_traces<N: Rep3NetworkExt>(
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

        let (hashes, trace) =
            poseidon2.hash_rep3_generate_noir_trace_many::<_, 2, 4>(input, &mut precompute, net)?;
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
