#[oracle(__debug_poseidon_start)]
unconstrained fn __debug_poseidon_start() {}
#[oracle(__debug_poseidon_end)]
unconstrained fn __debug_poseidon_end() {}

unconstrained fn mark_poseidon_start() {
    __debug_poseidon_start()
}
unconstrained fn mark_poseidon_end() {
    __debug_poseidon_end()
}

fn safe_mark_poseidon_start() {
    // Safety: This function is only a marker
    unsafe {
        mark_poseidon_start();
    }
}
fn safe_mark_poseidon_end() {
    // Safety: This function is only a marker
    unsafe {
        mark_poseidon_end();
    }
}

// Hashing as a compression function with t=2 and feed-forward
pub(crate) fn hash2(left: Field, right: Field) -> Field {
    safe_mark_poseidon_start();
    let state = poseidon2::bn254::hash_2([left, right]);
    safe_mark_poseidon_end();
    state + left // Feed forward
}

pub fn commit1(value: Field, r: Field) -> Field {
    crate::hash::hash2(value, r)
}
