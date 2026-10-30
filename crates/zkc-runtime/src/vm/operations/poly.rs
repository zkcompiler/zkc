//! Installed poly operation implementations and physical policy.
use super::*;

pub(super) const CONTRACTS: &[Installation] = &[
    Installation::selectable("ring.point").implemented_by(&["plonky3/ring.point"]),
    Installation::selectable("ring.rows").implemented_by(&["plonky3/ring.rows"]),
    Installation::selectable("ring.coefficients").implemented_by(&["plonky3/ring.coefficients"]),
    Installation::selectable("ring.affine_sum").implemented_by(&["plonky3/ring.affine_sum"]),
    Installation::selectable("poly.table_arity").implemented_by(&["arkworks/poly.table_arity"]),
    Installation::selectable("poly.coefficient_count").implemented_by(&[
        "arkworks/poly.coefficient_count",
        "dalek/poly.coefficient_count",
        "plonky3/poly.coefficient_count",
    ]),
    Installation::selectable("poly.coset_evaluate").implemented_by(&[
        "arkworks/poly.coset_evaluate",
        "plonky3/poly.coset_evaluate",
    ]),
    Installation::selectable("poly.coset_evaluate_batch").implemented_by(&[
        "arkworks/poly.coset_evaluate_batch",
        "plonky3/poly.coset_evaluate_batch",
    ]),
    Installation::selectable("poly.coset_extend")
        .implemented_by(&["arkworks/poly.coset_extend", "plonky3/poly.coset_extend"]),
    Installation::selectable("poly.coset_evaluate_at").implemented_by(&[
        "arkworks/poly.coset_evaluate_at",
        "plonky3/poly.coset_evaluate_at",
    ]),
    Installation::selectable("poly.coset_interpolate").implemented_by(&[
        "arkworks/poly.coset_interpolate",
        "plonky3/poly.coset_interpolate",
    ]),
    Installation::selectable("poly.domain_point")
        .implemented_by(&["arkworks/poly.domain_point", "plonky3/poly.domain_point"]),
    Installation::selectable("poly.domain_root")
        .implemented_by(&["arkworks/poly.domain_root", "plonky3/poly.domain_root"]),
    Installation::selectable("poly.domain_points")
        .implemented_by(&["arkworks/poly.domain_points", "plonky3/poly.domain_points"]),
    Installation::selectable("poly.even_odd_fold")
        .implemented_by(&["arkworks/poly.even_odd_fold", "plonky3/poly.even_odd_fold"]),
    Installation::selectable("poly.divide_opening").implemented_by(&[
        "arkworks/poly.divide_opening",
        "dalek/poly.divide_opening",
        "plonky3/poly.divide_opening",
    ]),
    Installation::selectable("poly.opening_quotient").implemented_by(&[
        "arkworks/poly.opening_quotient",
        "plonky3/poly.opening_quotient",
    ]),
    Installation::selectable("poly.opening_quotient_sum").implemented_by(&[
        "arkworks/poly.opening_quotient_sum",
        "plonky3/poly.opening_quotient_sum",
    ]),
    Installation::selectable("poly.equality_weights")
        .implemented_by(&["arkworks/poly.equality_weights"]),
    Installation::selectable("poly.from_coefficients").implemented_by(&[
        "arkworks/poly.from_coefficients",
        "dalek/poly.from_coefficients",
        "plonky3/poly.from_coefficients",
    ]),
    Installation::selectable("poly.coefficients").implemented_by(&[
        "arkworks/poly.coefficients",
        "dalek/poly.coefficients",
        "plonky3/poly.coefficients",
    ]),
    Installation::selectable("poly.degree_check").implemented_by(&[
        "arkworks/poly.degree_check",
        "dalek/poly.degree_check",
        "plonky3/poly.degree_check",
    ]),
    Installation::selectable("poly.univariate_evaluate").implemented_by(&[
        "arkworks/poly.univariate_evaluate",
        "dalek/poly.univariate_evaluate",
        "plonky3/poly.univariate_evaluate",
    ]),
    Installation::selectable("poly.univariate_boundary").implemented_by(&[
        "arkworks/poly.univariate_boundary",
        "dalek/poly.univariate_boundary",
        "plonky3/poly.univariate_boundary",
    ]),
    Installation::selectable("poly.product_sum").implemented_by(&["arkworks/poly.product_sum"]),
    Installation::selectable("poly.product_round").implemented_by(&["arkworks/poly.product_round"]),
    Installation::selectable("poly.boundary").implemented_by(&[
        "arkworks/poly.boundary",
        "dalek/poly.boundary",
        "plonky3/poly.boundary",
    ]),
    Installation::selectable("poly.round_evaluate").implemented_by(&[
        "arkworks/poly.round_evaluate",
        "dalek/poly.round_evaluate",
        "plonky3/poly.round_evaluate",
    ]),
    Installation::selectable("poly.fold").implemented_by(&["arkworks/poly.fold"]),
    Installation::selectable("poly.evaluate").implemented_by(&["arkworks/poly.evaluate"]),
    Installation::selectable("poly.empty_point").implemented_by(&["arkworks/poly.empty_point"]),
    Installation::selectable("poly.append_point").implemented_by(&["arkworks/poly.append_point"]),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: ALTERNATIVES,
    physical_error: "uninstalled operation binding",

    contracts: CONTRACTS,

    select,
};

/// The ring provider substitutes integer residue coordinates, so no binary
/// field is implemented, although the logical contract needs only a field.
fn select(
    binding: &OperationBinding,
    logical: &OperationSignature<LogicalType>,
    selection: Selection,
) -> Result<BoundSignature> {
    if binding.contract.starts_with("ring.")
        && !support::primary(binding)?.has_residue_coordinates()
    {
        return Err(support::failure());
    }
    support::select_nominal(binding, logical, selection)
}

use super::super::domain_bindings::PortTransform;
const ALTERNATIVES: &[Alternative] = &[
    Alternative {
        timing: TimingRequirement::Unspecified,
        implementation: "arkworks-msb/poly.product_sum",
        contract: "poly.product_sum",
        domains: &[Identity::Bls12381Fr],
        ports: PortTransform::Msb,
    },
    Alternative {
        timing: TimingRequirement::Unspecified,
        implementation: "arkworks-msb/poly.product_round",
        contract: "poly.product_round",
        domains: &[Identity::Bls12381Fr],
        ports: PortTransform::Msb,
    },
    Alternative {
        timing: TimingRequirement::Unspecified,
        implementation: "arkworks-msb/poly.boundary",
        contract: "poly.boundary",
        domains: &[Identity::Bls12381Fr],
        ports: PortTransform::Msb,
    },
    Alternative {
        timing: TimingRequirement::Unspecified,
        implementation: "arkworks-msb/poly.round_evaluate",
        contract: "poly.round_evaluate",
        domains: &[Identity::Bls12381Fr],
        ports: PortTransform::Msb,
    },
    Alternative {
        timing: TimingRequirement::Unspecified,
        implementation: "arkworks-msb/poly.fold",
        contract: "poly.fold",
        domains: &[Identity::Bls12381Fr],
        ports: PortTransform::Msb,
    },
    Alternative {
        timing: TimingRequirement::Unspecified,
        implementation: "arkworks-msb/poly.evaluate",
        contract: "poly.evaluate",
        domains: &[Identity::Bls12381Fr],
        ports: PortTransform::Msb,
    },
    Alternative {
        timing: TimingRequirement::Unspecified,
        implementation: "arkworks-msb/poly.empty_point",
        contract: "poly.empty_point",
        domains: &[Identity::Bls12381Fr],
        ports: PortTransform::Msb,
    },
    Alternative {
        timing: TimingRequirement::Unspecified,
        implementation: "arkworks-msb/poly.append_point",
        contract: "poly.append_point",
        domains: &[Identity::Bls12381Fr],
        ports: PortTransform::Msb,
    },
];
