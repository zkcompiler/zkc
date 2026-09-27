//! Logical units use the same authenticated resource store as random, nonce,
//! and transcript capabilities.
use super::NativeBackend;
use crate::{Result, Value, refused};
use zkc_runtime::interactive::{
    AttributeRule, BoundSignature, Invocation, KernelSignature, LogicalType, OperationBinding,
    PhysicalType,
};
pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    let [domain] = binding.arguments.as_slice() else {
        return None;
    };
    if binding.implementation != format!("logical/{}", binding.contract) {
        return None;
    }
    let ty = PhysicalType::default_for(LogicalType::resource_unit(
        zkc_runtime::interactive::ResourceDomain::parse(domain).ok()?,
    ))
    .ok()?;
    let (inputs, outputs) = match binding.contract.as_str() {
        "resource_unit.create" => (vec![], vec![ty]),
        "resource_unit.pass" => (vec![ty.clone()], vec![ty]),
        "resource_unit.consume" => (vec![ty], vec![]),
        _ => return None,
    };
    Some(KernelSignature {
        inputs,
        outputs,
        attributes: AttributeRule::None,
    })
}
pub(super) fn execute(
    backend: &mut NativeBackend,
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
