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
            | "poly.coset_extend"
            | "poly.coset_evaluate_at"
            | "poly.coset_interpolate"
            | "poly.domain_point"
            | "poly.domain_root"
            | "poly.domain_points"
            | "poly.even_odd_fold"
            | "poly.opening_quotient"
    ) && !matches!(
        domain.field,
        Identity::Bn254Fr | Identity::KoalaBear | Identity::KoalaBearExt8 | Identity::KoalaBearExt4
    ) {
        return None;
    }
    if binding.contract == "poly.even_odd_fold" && !domain.field.has_characteristic_not_two() {
        return None;
    }
    // Ring arenas substitute integer residue coordinates.
    if binding.contract.starts_with("ring.") && !domain.field.has_residue_coordinates() {
        return None;
    }
    support::domain_signature(binding, row, selection, domain)
}

/// Independent native port facts, also used for exact implementation assembly.
pub(crate) const COSET_CONTRACTS: &[crate::bindings::Contract] = {
    use zkc_runtime::vm::{AttributeRule, Type::*};
    &[
        operation(
            "poly.coset_evaluate_at",
            &[Vector, Index, Index, Field, Field],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/poly.coset_evaluate_at",
            "plonky3/poly.coset_evaluate_at",
        ]),
        operation(
            "poly.coset_extend",
            &[Vector, Index, Index, Field, Field, Index],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&["arkworks/poly.coset_extend", "plonky3/poly.coset_extend"]),
        operation(
            "poly.coset_evaluate",
            &[Polynomial, Field, Index],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/poly.coset_evaluate",
            "plonky3/poly.coset_evaluate",
        ]),
        operation(
            "poly.coset_interpolate",
            &[Vector, Field],
            &[Polynomial],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/poly.coset_interpolate",
            "plonky3/poly.coset_interpolate",
        ]),
        operation(
            "poly.domain_point",
            &[Field, Index, Index],
            &[Field],
            AttributeRule::None,
        )
        .implemented_by(&["arkworks/poly.domain_point", "plonky3/poly.domain_point"]),
        operation("poly.domain_root", &[Index], &[Field], AttributeRule::None)
            .implemented_by(&["arkworks/poly.domain_root", "plonky3/poly.domain_root"]),
        operation(
            "poly.domain_points",
            &[Field, Index],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&["arkworks/poly.domain_points", "plonky3/poly.domain_points"]),
        operation(
            "poly.even_odd_fold",
            &[Vector, Field, Field],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&["arkworks/poly.even_odd_fold", "plonky3/poly.even_odd_fold"]),
        operation(
            "poly.opening_quotient",
            &[Vector, Field, Field, Field],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/poly.opening_quotient",
            "plonky3/poly.opening_quotient",
        ]),
    ]
};
