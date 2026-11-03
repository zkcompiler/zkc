//! Domain-free Boolean operations have a fixed native implementation.
use super::*;
use zkc_runtime::vm::PhysicalType;
pub(crate) const fn operation(name: &'static str) -> Contract {
    Contract::new(name, resolve)
}
fn resolve(
    binding: &OperationBinding,
    _row: &Contract,
    selection: Selection,
) -> Option<BoundSignature> {
    if !binding.arguments.is_empty() || !matches!(selection, Selection::Default) {
        return None;
    }
    let ports = support::ports(binding, selection, "arkworks")?;
    support::materialize(binding, ports, |logical| {
        PhysicalType::default_for(logical.clone()).ok()
    })
}
