//! Fixed native randomness operations.
use super::*;
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
    if !matches!(selection, Selection::Default) {
        return None;
    }
    let domain = support::field_domain(binding)?;
    if binding.contract == "random.index" && domain.field != Identity::KoalaBearExt8 {
        return None;
    }
    support::domain_signature(binding, row, selection, domain)
}
