//! Polynomial family restrictions remain visible beside its signature resolver.
use super::*;
pub(crate) const fn operation(name: &'static str) -> Contract {
    Contract::new(name, resolve).selectable()
}
fn resolve(
    binding: &OperationBinding,
    _row: &Contract,
    selection: Selection,
) -> Option<BoundSignature> {
    let domain = support::field_domain(binding)?;
    // Coset and domain kernels need the field's installed two-adic subgroup.
    if COSET_CONTRACTS
        .iter()
        .any(|row| row.name == binding.contract)
        && !domain.field.holds("TwoAdicField")
    {
        return None;
    }
    if binding.contract == "poly.even_odd_fold" && !domain.field.has_characteristic_not_two() {
        return None;
    }
    // Ring arenas substitute integer residue coordinates.
    if binding.contract.starts_with("ring.") && !domain.field.has_residue_coordinates() {
        return None;
    }
    support::domain_signature(binding, selection, domain)
}

/// Native implementations of catalog contracts. Ports and parameter rules
/// come from each declaration; rows name only contract and implementation.
pub(crate) const COSET_CONTRACTS: &[crate::bindings::Contract] = {
    &[
        operation("poly.coset_evaluate_batch").implemented_by(&[
            "arkworks/poly.coset_evaluate_batch",
            "plonky3/poly.coset_evaluate_batch",
        ]),
        operation("poly.coset_evaluate_at").implemented_by(&[
            "arkworks/poly.coset_evaluate_at",
            "plonky3/poly.coset_evaluate_at",
        ]),
        operation("poly.coset_extend")
            .implemented_by(&["arkworks/poly.coset_extend", "plonky3/poly.coset_extend"]),
        operation("poly.coset_evaluate").implemented_by(&[
            "arkworks/poly.coset_evaluate",
            "plonky3/poly.coset_evaluate",
        ]),
        operation("poly.coset_interpolate").implemented_by(&[
            "arkworks/poly.coset_interpolate",
            "plonky3/poly.coset_interpolate",
        ]),
        operation("poly.domain_point")
            .implemented_by(&["arkworks/poly.domain_point", "plonky3/poly.domain_point"]),
        operation("poly.domain_root")
            .implemented_by(&["arkworks/poly.domain_root", "plonky3/poly.domain_root"]),
        operation("poly.domain_points")
            .implemented_by(&["arkworks/poly.domain_points", "plonky3/poly.domain_points"]),
        operation("poly.even_odd_fold")
            .implemented_by(&["arkworks/poly.even_odd_fold", "plonky3/poly.even_odd_fold"]),
        operation("poly.opening_quotient").implemented_by(&[
            "arkworks/poly.opening_quotient",
            "plonky3/poly.opening_quotient",
        ]),
        operation("poly.opening_quotient_sum").implemented_by(&[
            "arkworks/poly.opening_quotient_sum",
            "plonky3/poly.opening_quotient_sum",
        ]),
    ]
};
