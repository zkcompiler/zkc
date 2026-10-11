//! Declared operand read extents for kernels that access part of an operand.
//! The Runner charges every other kernel the full retained bytes of every
//! operand. Each extent bounds the kernel body's operand reads. Native nested
//! admission and backing walks are bounded by the sequence-work ledger.
use crate::Value;

/// Charge for one scalar, index or handle operand, as for an inline value.
const HANDLE: usize = 512;

pub(super) fn operand_work(contract: &str, args: &[Value]) -> Option<u64> {
    let bytes = match (contract, args) {
        // One row and its authentication path, plus the row index.
        ("oracle.open", [Value::OracleState(state), Value::Index(_)]) => {
            state.opening_bytes().ok()?.checked_add(HANDLE)?
        }
        // One element or handle selected from a collection, plus the index.
        (
            "opening_states.at" | "commitments.at" | "vector.get" | "field_array.get",
            [_, Value::Index(_)],
        ) => 2 * HANDLE,
        ("field_array.at", [_]) => HANDLE,
        ("sequence.at", [Value::Sequence(sequence), Value::Index(_)]) => {
            return Some(sequence.access_work());
        }
        ("sequence.append", [Value::Sequence(sequence), value]) => {
            return sequence.append_work(value);
        }
        // The stored length only.
        (
            "opening_states.length"
            | "commitments.length"
            | "sequence.length"
            | "vector.length"
            | "poly.coefficient_count",
            [_],
        ) => HANDLE,
        _ => return None,
    };
    Some(bytes as u64)
}
