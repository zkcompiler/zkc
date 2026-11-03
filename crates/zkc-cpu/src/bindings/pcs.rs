//! Installed multilinear commitment scheme admission.
use super::*;
pub(crate) const fn operation(name: &'static str) -> Contract {
    Contract::new(name, resolve).selectable()
}
fn resolve(
    binding: &OperationBinding,
    _row: &Contract,
    selection: Selection,
) -> Option<BoundSignature> {
    if binding.arguments != ["multilinear.kzg.bls12-381/0"] {
        return None;
    }
    support::domain_signature(binding, selection, crate::domains::BLS)
}
