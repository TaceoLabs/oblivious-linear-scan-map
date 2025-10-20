// Compile with: nargo compile --expression-width=1000 --bounded-codegen

// Returns the Merkle root and the commitment to the index
fn main(
    leaf: Field,
    key_bits: [Field; 32],
    hash_path: [Field; 32],
    r: Field,
) -> pub (Field, Field) {
    oblivious_map::read(leaf, key_bits, hash_path, r)
}
