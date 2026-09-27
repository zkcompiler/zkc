//! Polynomial family restrictions remain visible beside its signature resolver.
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
    let domain = support::field_domain(binding)?;
    if matches!(
        binding.contract.as_str(),
        "poly.coset_evaluate"
            | "poly.coset_interpolate"
            | "poly.domain_point"
            | "poly.domain_root"
            | "poly.domain_points"
            | "poly.even_odd_fold"
            | "poly.opening_quotient"
    ) && !matches!(
        domain.field,
        Identity::Bn254Fr | Identity::KoalaBear | Identity::KoalaBearExt8
    ) {
        return None;
    }
    if binding.contract == "poly.even_odd_fold" && !domain.field.has_characteristic_not_two() {
        return None;
    }
    support::domain_signature(binding, row, selection, domain)
}
