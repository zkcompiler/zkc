//! Logical units use the same authenticated resource store as random, nonce,
//! and transcript capabilities.
use super::CpuBackend;
use crate::{Result, Value, refused};
use zkc_runtime::vm::{BoundSignature, Invocation, OperationBinding};
/// The catalog-resolved signature of the logical implementation.
pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    if binding.implementation != format!("logical/{}", binding.contract) {
        return None;
    }
    binding.signature().ok()
}
pub(super) fn execute(
    backend: &mut CpuBackend,
    i: &Invocation<'_>,
    args: &[Value],
) -> Result<Vec<Value>> {
    use Value::*;
    let name = i.binding.declaration().contract.as_str();
    let values = match (name, args) {
        ("resource_unit.create", []) => {
            backend.core.policy.output(512, i.max_output_bytes)?;
            vec![
                backend.core.resources.create_unit(
                    i.frame,
                    i.binding
                        .signature()
                        .outputs
                        .first()
                        .ok_or_else(|| refused("kernel-operands"))?
                        .logical()
                        .resource_domain()
                        .ok_or_else(|| refused("kernel-operands"))?,
                )?,
            ]
        }
        ("resource_unit.pass", [ResourceUnit(token)]) => {
            backend.core.policy.output(512, i.max_output_bytes)?;
            vec![
                backend
                    .core
                    .resources
                    .pass_unit(i.frame, token.capability())?,
            ]
        }
        ("resource_unit.consume", [ResourceUnit(token)]) => {
            backend
                .core
                .resources
                .consume_unit(i.frame, token.capability())?;
            vec![]
        }
        _ => return Err(refused("kernel-operands")),
    };
    Ok(values)
}
