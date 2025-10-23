use ark_ff::Zero as _;
use co_noir::{Bn254, Rep3AcvmType};
use co_noir_to_r1cs::trace::MpcTraceHasher;
use itertools::{Itertools as _, izip};

use mpc_core::{
    MpcState as _,
    gadgets::poseidon2::Poseidon2,
    protocols::{
        rep3::{self, Rep3PrimeFieldShare, Rep3State, network::Rep3NetworkExt},
        rep3_ring::Rep3RingShare,
    },
};
use tracing::instrument;

use crate::{LINEAR_SCAN_TREE_DEPTH, LinearScanObliviousMap, PathAndWitness, READ_PROOF_INPUTS};

struct ReadWithTrace {
    read_value: Rep3PrimeFieldShare<ark_bn254::Fr>,
    inputs: Vec<Rep3AcvmType<ark_bn254::Fr>>,
    traces: Vec<Vec<Rep3AcvmType<ark_bn254::Fr>>>,
}

/// Request for a read operation on the oblivious Merkle tree.
///
/// Contains the secret-shared key to read and secret-shared randomness used to commit to the key.
#[derive(Clone, Copy)]
pub struct ObliviousReadRequest {
    /// Secret-shared key identifying the target leaf.
    pub key: Rep3RingShare<u32>,
    /// Secret-shared randomness used for the key commitment.
    pub randomness_commitment: Rep3PrimeFieldShare<ark_bn254::Fr>,
}

/// Response to an oblivious read operation.
///
/// Includes the read value, a co-SNARK proving correctness, and the public inputs for verification:
/// - `root`: The Merkle tree root at the time of the read.
/// - `commitment`: The computed commitment to the key, calculated as Poseidon2(key, r) + idx.
pub struct ObliviousReadResult {
    /// Secret-shared value stored at the leaf corresponding to the key.
    pub read: Rep3PrimeFieldShare<ark_bn254::Fr>,
    /// Co-SNARK proof attesting to the read operation.
    pub proof: ark_groth16::Proof<Bn254>,
    /// Merkle root used for this read.
    pub root: ark_bn254::Fr,
    /// Commitment to the key, as Poseidon2(key, r) + idx.
    pub commitment: ark_bn254::Fr,
}

impl LinearScanObliviousMap {
    /// Reads the leaf value associated with the provided secret-shared key from the oblivious Merkle tree.
    ///
    /// Read operations can be processed in parallel, but must not overlap with insert or update operations.
    /// Computes a co-SNARK proof for the read, returning the leaf value, proof, and relevant public inputs.
    ///
    /// Needs two network streams that are disjunct from each other for internal parallelizing.
    ///
    /// # Returns
    /// An [`ObliviousReadResult`] containing:
    /// - The secret-shared leaf value
    /// - A co-SNARK proof attesting to the read
    /// - The Merkle root and key commitment as public inputs
    ///
    /// # Errors
    /// Returns an error only if a network failure occurs during the read protocol.
    #[instrument(level = "debug", skip_all)]
    pub fn oblivious_read<N: Rep3NetworkExt>(
        &self,
        req: ObliviousReadRequest,
        net0: &N,
        net1: &N,
        state0: &mut Rep3State,
    ) -> eyre::Result<ObliviousReadResult> {
        let ObliviousReadRequest {
            key,
            randomness_commitment,
        } = req;

        let mut state1 = state0.fork(1).expect("cannot fail for rep3");
        // Read the path and the witness from the tree.
        // We do this so we can do all the Poseidon2 runs at the same time, reducing the multiplicative-depth of the protocol. This of course increases the amount of bytes we need to send over the network by two.
        tracing::debug!("starting with reading the path and witness");
        let path_and_witness = self.read_path_and_witness(key, net0, net1, state0, &mut state1)?;
        // we could theocratically the key decomposition in parallel with another network, but the key decomposition is negligible in contrast to AND-tree and the poseidon hashes so we stick with this.
        tracing::debug!("decomposing key...");
        let bitinject = Self::key_decompose(key, net0, state0)?;

        // build the poseidon execution traces for the proof.
        tracing::debug!("building read execution trace");
        let trace = self.build_read_execution_trace(
            path_and_witness,
            bitinject,
            randomness_commitment,
            net0,
            net1,
            state0,
            &mut state1,
        )?;
        tracing::debug!("creating co-SNARK");
        self.groth16_read_proof(net0, net1, trace, state0)
    }

    /// Performs the read-groth16 proof.
    #[instrument(level = "debug", skip_all)]
    fn groth16_read_proof<N: Rep3NetworkExt>(
        &self,
        net0: &N,
        net1: &N,
        read_with_trace: ReadWithTrace,
        state0: &mut Rep3State,
    ) -> eyre::Result<ObliviousReadResult> {
        let ReadWithTrace {
            read_value,
            inputs,
            traces,
        } = read_with_trace;

        let (proof, public_inputs) =
            Self::co_snark(inputs, traces, &self.read_groth16, net0, net1, state0)?;
        tracing::trace!("> groth16 read proof");

        debug_assert_eq!(public_inputs[0], self.root);
        Ok(ObliviousReadResult {
            read: read_value,
            proof,
            root: public_inputs[0],
            commitment: public_inputs[1],
        })
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
    #[expect(clippy::too_many_arguments)]
    fn build_read_execution_trace<N: Rep3NetworkExt>(
        &self,
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
            Self::join(
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
}

#[cfg(test)]
mod tests {
    use co_noir_to_r1cs::noir::r1cs;
    use mpc_core::protocols::{
        rep3::{self, Rep3State, conversion::A2BType},
        rep3_ring::{self, ring::ring_impl::RingElement},
    };
    use mpc_net::local::LocalNetwork;

    use crate::{LinearScanObliviousMap, ObliviousReadRequest, tests::groth16_material};
    #[test]
    fn read_empty_map() -> eyre::Result<()> {
        let mut rng = rand::thread_rng();

        // generate a random key
        let key = RingElement(rand::random::<u32>());
        let randomness_commitment = ark_bn254::Fr::from(rand::random::<u128>());

        let [key_share0, key_share1, key_share2] =
            rep3_ring::share_ring_element_binary(key, &mut rng);

        let [r0, r1, r2] = rep3::share_field_element(randomness_commitment, &mut rng);

        // need two networks
        let [n0, n1, n2] = LocalNetwork::new_3_parties();
        let [n3, n4, n5] = LocalNetwork::new_3_parties();
        let random_default_value = ark_bn254::Fr::from(rand::random::<u128>());

        let material0 = groth16_material()?;
        let material1 = material0.clone();
        let material2 = material0.clone();
        let read_vk = material0.0.pk.vk.clone();

        let [res0, res1, res2] = std::thread::scope(|s| {
            let res0 = s.spawn(|| {
                let (read_groth16, write_groth16) = material0;
                let map = LinearScanObliviousMap::with_default_value(
                    random_default_value,
                    read_groth16,
                    write_groth16,
                );
                let mut state = Rep3State::new(&n0, A2BType::Direct).expect("works");
                let req = ObliviousReadRequest {
                    key: key_share0,
                    randomness_commitment: r0,
                };
                map.oblivious_read(req, &n0, &n3, &mut state)
            });

            let res1 = s.spawn(|| {
                let (read_groth16, write_groth16) = material1;
                let map = LinearScanObliviousMap::with_default_value(
                    random_default_value,
                    read_groth16,
                    write_groth16,
                );
                let mut state = Rep3State::new(&n1, A2BType::Direct).expect("works");
                let req = ObliviousReadRequest {
                    key: key_share1,
                    randomness_commitment: r1,
                };
                map.oblivious_read(req, &n1, &n4, &mut state)
            });

            let res2 = s.spawn(|| {
                let (read_groth16, write_groth16) = material2;
                let map = LinearScanObliviousMap::with_default_value(
                    random_default_value,
                    read_groth16,
                    write_groth16,
                );
                let mut state = Rep3State::new(&n2, A2BType::Direct).expect("works");
                let req = ObliviousReadRequest {
                    key: key_share2,
                    randomness_commitment: r2,
                };
                map.oblivious_read(req, &n2, &n5, &mut state)
            });
            let res0 = res0.join().expect("can join").expect("did work");
            let res1 = res1.join().expect("can join").expect("did work");
            let res2 = res2.join().expect("can join").expect("did work");
            [res0, res1, res2]
        });

        let read_value = (res0.read + res1.read + res2.read).a;
        assert_eq!(read_value, random_default_value);

        // verify the proofs
        assert!(r1cs::verify(
            &read_vk,
            &res0.proof,
            &[res0.root, res0.commitment]
        )?);
        assert!(r1cs::verify(
            &read_vk,
            &res1.proof,
            &[res1.root, res1.commitment]
        )?);
        assert!(r1cs::verify(
            &read_vk,
            &res2.proof,
            &[res2.root, res2.commitment]
        )?);

        Ok(())
    }
}
