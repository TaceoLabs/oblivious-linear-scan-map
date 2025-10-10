pub(crate) mod merkle;
pub(crate) mod hash;

pub fn commit_index<let N: u32>(index_bits: [Field; N], r: Field) -> Field {
    // index bits are either 0 or 1, this is checked in compute_merkle_root
    let mut index = 0;
    for i in 0..N {
        index *= 2;
        index += index_bits[N - 1 - i];
    }
    crate::hash::commit1(index, r)
}

// Returns the Merkle root and the commitment to the index
pub fn read<let N: u32>(
    leaf: Field,
    index_bits: [Field; N],
    hash_path: [Field; N],
    r: Field,
) -> (Field, Field) {
    let root = merkle::compute_merkle_root(leaf, index_bits, hash_path);
    let commitment = commit_index(index_bits, r);
    (root, commitment)
}

// Returns the old Merkle root as well as the new Merkle root. Also returns the commitment to the index and the commitment to the new value.
pub fn write<let N: u32>(
    old_leaf: Field,
    new_leaf: Field,
    index_bits: [Field; N],
    hash_path: [Field; N],
    r_index: Field,
    r_value: Field,
) -> (Field, Field, Field, Field) {
    let old_root = merkle::compute_merkle_root(old_leaf, index_bits, hash_path);
    let new_root = merkle::compute_merkle_root(new_leaf, index_bits, hash_path);
    let commitment_index = commit_index(index_bits, r_index);
    let commitment_value = crate::hash::commit1(new_leaf, r_value);
    (old_root, new_root, commitment_index, commitment_value)
}

// Returns the old Merkle root as well as the new Merkle root. Also returns the commitment to the index.
pub fn delete<let N: u32>(
    old_leaf: Field,
    index_bits: [Field; N],
    hash_path: [Field; N],
    r_index: Field,
) -> (Field, Field, Field) {
    let deleted_leaf = 0xDEADBEEF;
    let old_root = merkle::compute_merkle_root(old_leaf, index_bits, hash_path);
    let new_root = merkle::compute_merkle_root(deleted_leaf, index_bits, hash_path);
    let commitment = commit_index(index_bits, r_index);
    (old_root, new_root, commitment)
}
