//! Current native wire codec and setup requirements.
pub(crate) mod native;
pub use native::{NativeInputSize, NativeWireError, has_native_wire, native_wire_size};
use zkc_runtime::interactive::{Identity, LogicalType, Type};
pub fn requires_setup(ty: LogicalType) -> bool {
    ty.sequence_element()
        .is_some_and(|t| requires_setup(t.clone()))
        || ty.variant_descriptor().is_some_and(|d| {
            d.alternatives()
                .iter()
                .any(|a| a.payload().iter().any(|t| requires_setup(t.clone())))
        })
        || ty.identity() == Identity::MultilinearKzgBls12381
            && matches!(ty.kind(), Type::Commitment | Type::Proof)
}
const MAGIC: &[u8] = b"ZKCV\x01";
fn decode_bool(body: &[u8]) -> std::result::Result<bool, zkc_runtime::interactive::DecodeReason> {
    match body {
        [0] => Ok(false),
        [1] => Ok(true),
        _ => Err(zkc_runtime::interactive::DecodeReason::Boolean),
    }
}
