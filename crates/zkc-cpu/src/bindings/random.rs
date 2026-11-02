//! Fixed native randomness operations.
use super::*;
pub(crate) const fn operation(name: &'static str) -> Contract {
    Contract::new(name, resolve)
}
fn resolve(
    binding: &OperationBinding,
    _row: &Contract,
    selection: Selection,
) -> Option<BoundSignature> {
    if !matches!(selection, Selection::Default) {
        return None;
    }
    let domain = support::field_domain(binding)?;
    // UniformIndex sampling needs the field's installed index randomness.
    if binding.contract == "random.index" && !domain.field.holds("IndexRandomness") {
        return None;
    }
    support::domain_signature(binding, selection, domain)
}
