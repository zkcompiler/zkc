//! Installed operand read extents. Classification is static; sizes and sequence
//! traversal still depend on the actual arguments at every invocation.
use crate::Value;

/// Charge for one scalar, index or handle operand, as for an inline value.
const HANDLE: usize = crate::VALUE_SLOT_BYTES;

pub(super) enum ReadExtent {
    Full,
    Row,
    Rows,
    Indexed,
    Element,
    SequenceAt,
    SequenceAppend,
    Header,
}
impl ReadExtent {
    pub(super) fn for_contract(contract: &str) -> Self {
        match contract {
            "oracle.open" => Self::Row,
            "oracle.open_many" => Self::Rows,
            "opening_states.at" | "commitments.at" | "vector.get" | "field_array.get" => {
                Self::Indexed
            }
            "field_array.at" => Self::Element,
            "sequence.at" => Self::SequenceAt,
            "sequence.append" => Self::SequenceAppend,
            "opening_states.length"
            | "commitments.length"
            | "sequence.length"
            | "vector.length"
            | "poly.coefficient_count" => Self::Header,
            _ => Self::Full,
        }
    }
    pub(super) fn bytes(&self, args: &[Value]) -> Option<u64> {
        let bytes = match (self, args) {
            (Self::Row, [Value::OracleState(state), Value::Index(_)]) => {
                state.opening_bytes().ok()?.checked_add(HANDLE)?
            }
            (Self::Row, [Value::MerkleTree(state), Value::Index(_)]) => {
                state.opening_bytes(1).ok()?.checked_add(HANDLE)?
            }
            // Each requested position reads its row and at most its full path.
            (Self::Rows, [Value::OracleState(state), Value::Indices(positions)]) => state
                .opening_bytes()
                .ok()?
                .checked_mul(positions.len())?
                .checked_add(HANDLE)?
                .checked_add(positions.len().checked_mul(8)?)?
                .min(state.retained_bytes().ok()?.checked_add(HANDLE)?),
            (Self::Rows, [Value::MerkleTree(state), Value::Indices(positions)]) => state
                .opening_bytes(positions.len())
                .ok()?
                .checked_add(HANDLE)?
                .checked_add(positions.len().checked_mul(8)?)?
                .min(state.retained_bytes().ok()?.checked_add(HANDLE)?),
            (Self::Indexed, [_, Value::Index(_)]) => 2 * HANDLE,
            (Self::Element | Self::Header, [_]) => HANDLE,
            (Self::SequenceAt, [Value::Sequence(sequence), Value::Index(_)]) => {
                return Some(sequence.access_work());
            }
            (Self::SequenceAppend, [Value::Sequence(sequence), value]) => {
                return sequence.append_work(value);
            }
            _ => return None,
        };
        Some(bytes as u64)
    }
}
