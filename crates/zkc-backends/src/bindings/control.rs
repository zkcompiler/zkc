//! Domain-free Boolean operations have a fixed native implementation.
use super::*;
use zkc_runtime::interactive::{LogicalType, PhysicalType};
pub(crate) const fn operation(
    name: &'static str,
    inputs: &'static [Type],
    outputs: &'static [Type],
    attributes: AttributeRule,
) -> Contract {
    Contract::new(name, inputs, outputs, attributes, resolve)
}
fn resolve(
    binding: &OperationBinding,
    row: &Contract,
    selection: Selection,
) -> Option<BoundSignature> {
    if !binding.arguments.is_empty() || !matches!(selection, Selection::Default) {
        return None;
    }
    let ports = support::ports(binding, selection, "arkworks")?;
    support::materialize(row, Identity::None, ports, |kind| {
        PhysicalType::default_for(LogicalType::new(kind, Identity::None).ok()?).ok()
    })
}
