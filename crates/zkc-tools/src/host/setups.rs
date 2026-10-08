//! Setup checks shared by native invocation hosts. Authority maps stay with each host.
use super::inputs::Result;
use zkc_backends::Value;
use zkc_runtime::interactive::{LogicalType, Type};
pub(crate) fn needs_input_setup(ty: &LogicalType) -> bool {
    ty.kind() == Type::ProverKey || zkc_backends::requires_setup(ty.clone())
}
// Apply a port's configured setup recursively. Copyable aggregates may contain
// PCS leaves; neither aggregate construction nor unused entry data bypasses it.
pub(crate) fn check_input(value: &Value, key: &zkc_arkworks::VerifierKey) -> Result<()> {
    let metadata = match value {
        Value::Commitment(v) => Some(v.metadata()),
        Value::Proof(v) => Some(v.metadata()),
        Value::ProverKey(v) => Some(v.metadata()),
        Value::VerifierKey(v) => Some(v.metadata()),
        Value::Sequence(v) => {
            for child in v.elements() {
                check_input(child, key)?;
            }
            None
        }
        Value::Variant(v) => {
            for child in v.payload() {
                check_input(child, key)?;
            }
            None
        }
        _ => None,
    };
    if metadata.is_some_and(|actual| actual != key.metadata()) {
        return Err("native-proof-input-setup".into());
    }
    Ok(())
}
