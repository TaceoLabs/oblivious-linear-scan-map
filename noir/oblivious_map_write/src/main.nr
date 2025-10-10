// Compile with: nargo compile --expression-width=1000 --bounded-codegen

// Returns the old Merkle root as well as the new Merkle root. Also returns the commitment to the index and the commitment to the new value.
fn main(
    old_leaf: Field,
    new_leaf: Field,
    key_bits: [Field; 40],
    hash_path: [Field; 40],
    r_index: Field,
    r_value: Field,
) -> pub (Field, Field, Field, Field) {
    oblivious_map::write(old_leaf, new_leaf, key_bits, hash_path, r_index, r_value)
}
