//! Installed operand read extents. Classification is static; sizes and sequence
//! traversal still depend on the actual arguments at every invocation.
use crate::Value;

/// Charge for one scalar, index or handle operand, as for an inline value.
const HANDLE: usize = 512;

pub(super) enum ReadExtent {
    Full,
    Row,
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
