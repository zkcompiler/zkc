//! Installed multilinear commitment scheme admission.
use super::*;
pub(crate) const fn operation(
    name: &'static str,
    inputs: &'static [Type],
    outputs: &'static [Type],
    attributes: AttributeRule,
) -> Contract {
    Contract::new(name, inputs, outputs, attributes, resolve).selectable()
}
fn resolve(
    binding: &OperationBinding,
    row: &Contract,
    selection: Selection,
) -> Option<BoundSignature> {
    if binding.arguments != ["multilinear.kzg.bls12-381/1"] {
        return None;
    }
    support::domain_signature(binding, row, selection, crate::domains::BLS)
}
