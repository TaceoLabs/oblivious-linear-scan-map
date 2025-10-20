use co_circom::{ConstraintMatrices, ProvingKey};
use co_noir::Bn254;
use co_noir_to_r1cs::r1cs::noir_proof_schema::NoirProofScheme;

#[derive(Clone)]
pub struct Groth16Material {
    pub(crate) proof_schema: NoirProofScheme<ark_bn254::Fr>,
    pub(crate) cs: ConstraintMatrices<ark_bn254::Fr>,
    pub(crate) pk: ProvingKey<Bn254>,
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
