use crate::InsertTail;
use crate::ObliviousUpdateRequest;
use crate::UpdateTail;
use crate::base::MapBase;
use crate::cosnark::InsertWithTrace;

use mpc_core::{
    MpcState as _,
    protocols::rep3::{Rep3State, network::Rep3NetworkExt},
};

impl MapBase {
    pub(crate) fn insert_or_update<N: Rep3NetworkExt>(
        &mut self,
        update_request: ObliviousUpdateRequest,
        net0: &N,
        net1: &N,
        state0: &mut Rep3State,
    ) -> eyre::Result<InsertWithTrace> {
        let ObliviousUpdateRequest {
            key,
            update_value,
            randomness_index,
            randomness_commitment,
        } = update_request;
        // we need to check if the value is present in the leaf layer.
        // we do that by computing the ohv of the path and xor the leaf values.
        let mut state1 = state0.fork(1).expect("cant fail for rep3");

        let ((present_bit, path_ohv), (merkle_witness, bitinject)) = crate::join(
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
                update_value,
                path_ohv,
                merkle_witness,
                bitinject,
                randomness_index,
                randomness_commitment,
            };
            self.update_tail(update_tail, net0, net1, state0, &mut state1)
        } else {
            // not present - need to insert
            let insert_tail = InsertTail {
                key,
                insert_value: update_value,
                path_ohv: path_ohv[self.layers[0].values.len()..].to_vec(),
                merkle_witness,
                bitinject,
                randomness_index,
                randomness_commitment,
            };
            self.insert_tail(insert_tail, net0, net1, state0)
        }
    }
}
