//! Independently authored poly operation contracts and physical policy.
use super::*;
use Type::*;

pub(super) const CONTRACTS: &[Contract] = &[
    Contract::selectable(
        "poly.table_arity",
        (&[Table], &[Index], AttributeRule::None),
    )
    .implemented_by(&["arkworks/poly.table_arity"]),
    Contract::selectable(
        "poly.coefficient_count",
        (&[Polynomial], &[Index], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/poly.coefficient_count",
        "dalek/poly.coefficient_count",
        "plonky3/poly.coefficient_count",
    ]),
    Contract::selectable(
        "poly.coset_evaluate",
        (&[Polynomial, Field, Index], &[Vector], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/poly.coset_evaluate",
        "plonky3/poly.coset_evaluate",
    ]),
    Contract::selectable(
        "poly.coset_interpolate",
        (&[Vector, Field], &[Polynomial], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/poly.coset_interpolate",
        "plonky3/poly.coset_interpolate",
    ]),
    Contract::selectable(
        "poly.domain_point",
        (&[Field, Index, Index], &[Field], AttributeRule::None),
    )
    .implemented_by(&["arkworks/poly.domain_point", "plonky3/poly.domain_point"]),
    Contract::selectable(
        "poly.domain_root",
        (&[Index], &[Field], AttributeRule::None),
    )
    .implemented_by(&["arkworks/poly.domain_root", "plonky3/poly.domain_root"]),
    Contract::selectable(
        "poly.domain_points",
        (&[Field, Index], &[Vector], AttributeRule::None),
    )
    .implemented_by(&["arkworks/poly.domain_points", "plonky3/poly.domain_points"]),
    Contract::selectable(
        "poly.even_odd_fold",
        (&[Vector, Field, Field], &[Vector], AttributeRule::None),
    )
    .implemented_by(&["arkworks/poly.even_odd_fold", "plonky3/poly.even_odd_fold"]),
    Contract::selectable(
        "poly.divide_opening",
        (
            &[Polynomial, Field, Field],
            &[Polynomial],
            AttributeRule::None,
        ),
    )
    .implemented_by(&[
        "arkworks/poly.divide_opening",
        "dalek/poly.divide_opening",
        "plonky3/poly.divide_opening",
    ]),
    Contract::selectable(
        "poly.opening_quotient",
        (
            &[Vector, Field, Field, Field],
            &[Vector],
            AttributeRule::None,
        ),
    )
    .implemented_by(&[
        "arkworks/poly.opening_quotient",
        "plonky3/poly.opening_quotient",
    ]),
    Contract::selectable(
        "poly.equality_weights",
        (&[Point], &[Vector], AttributeRule::None),
    )
    .implemented_by(&["arkworks/poly.equality_weights"]),
    Contract::selectable(
        "poly.from_coefficients",
        (&[Vector], &[Polynomial], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/poly.from_coefficients",
        "dalek/poly.from_coefficients",
        "plonky3/poly.from_coefficients",
    ]),
    Contract::selectable(
        "poly.coefficients",
        (&[Polynomial], &[Vector], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/poly.coefficients",
        "dalek/poly.coefficients",
        "plonky3/poly.coefficients",
    ]),
    Contract::selectable(
        "poly.degree_check",
        (&[Polynomial], &[Bool], AttributeRule::NaturalIndex),
    )
    .implemented_by(&[
        "arkworks/poly.degree_check",
        "dalek/poly.degree_check",
        "plonky3/poly.degree_check",
    ]),
    Contract::selectable(
        "poly.univariate_evaluate",
        (&[Polynomial, Field], &[Field], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/poly.univariate_evaluate",
        "dalek/poly.univariate_evaluate",
        "plonky3/poly.univariate_evaluate",
    ]),
    Contract::selectable(
        "poly.univariate_boundary",
        (&[Polynomial], &[Field], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/poly.univariate_boundary",
        "dalek/poly.univariate_boundary",
        "plonky3/poly.univariate_boundary",
    ]),
    Contract::selectable(
        "poly.product_sum",
        (&[Table, Table], &[Field], AttributeRule::None),
    )
    .implemented_by(&["arkworks/poly.product_sum"]),
    Contract::selectable(
        "poly.product_round",
        (&[Table, Table], &[Round], AttributeRule::None),
    )
    .implemented_by(&["arkworks/poly.product_round"]),
    Contract::selectable("poly.boundary", (&[Round], &[Field], AttributeRule::None))
        .implemented_by(&[
            "arkworks/poly.boundary",
            "dalek/poly.boundary",
            "plonky3/poly.boundary",
        ]),
    Contract::selectable(
        "poly.round_evaluate",
        (&[Round, Field], &[Field], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/poly.round_evaluate",
        "dalek/poly.round_evaluate",
        "plonky3/poly.round_evaluate",
    ]),
    Contract::selectable(
        "poly.fold",
        (&[Table, Field], &[Table], AttributeRule::None),
    )
    .implemented_by(&["arkworks/poly.fold"]),
    Contract::selectable(
        "poly.evaluate",
        (&[Table, Point], &[Field], AttributeRule::None),
    )
    .implemented_by(&["arkworks/poly.evaluate"]),
    Contract::selectable("poly.empty_point", (&[], &[Point], AttributeRule::None))
        .implemented_by(&["arkworks/poly.empty_point"]),
    Contract::selectable(
        "poly.append_point",
        (&[Point, Field], &[Point], AttributeRule::None),
    )
    .implemented_by(&["arkworks/poly.append_point"]),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: ALTERNATIVES,
    physical_error: "uninstalled operation binding",
    physical_only: false,

    contracts: CONTRACTS,
    resolve,
    select: support::select_nominal,
};

fn resolve(
    binding: &OperationBinding,
    contract: &Contract,
) -> Result<KernelSignature<LogicalType>> {
    let shape = contract.shape()?;
    let primary = support::primary(binding)?;
    let field = primary.scalar_field().ok_or_else(support::failure)?;
    if binding.contract == "poly.even_odd_fold" && !field.has_characteristic_not_two() {
        return Err(support::failure());
    }
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
        field,
        Identity::Bn254Fr | Identity::KoalaBear | Identity::KoalaBearExt8
    ) {
        return Err(support::failure());
    }
    support::require_primary(binding, field)?;
    support::instantiate(shape, field, |kind| support::field_type(kind, field))
}

use super::super::domain_bindings::PortTransform;
const ALTERNATIVES: &[Alternative] = &[
    Alternative {
        implementation: "arkworks-msb/poly.product_sum",
        contract: "poly.product_sum",
        primary: Identity::Bls12381Fr,
        ports: PortTransform::Msb,
    },
    Alternative {
        implementation: "arkworks-msb/poly.product_round",
        contract: "poly.product_round",
        primary: Identity::Bls12381Fr,
        ports: PortTransform::Msb,
    },
    Alternative {
        implementation: "arkworks-msb/poly.boundary",
        contract: "poly.boundary",
        primary: Identity::Bls12381Fr,
        ports: PortTransform::Msb,
    },
    Alternative {
        implementation: "arkworks-msb/poly.round_evaluate",
        contract: "poly.round_evaluate",
        primary: Identity::Bls12381Fr,
        ports: PortTransform::Msb,
    },
    Alternative {
        implementation: "arkworks-msb/poly.fold",
        contract: "poly.fold",
        primary: Identity::Bls12381Fr,
        ports: PortTransform::Msb,
    },
    Alternative {
        implementation: "arkworks-msb/poly.evaluate",
        contract: "poly.evaluate",
        primary: Identity::Bls12381Fr,
        ports: PortTransform::Msb,
    },
    Alternative {
        implementation: "arkworks-msb/poly.empty_point",
        contract: "poly.empty_point",
        primary: Identity::Bls12381Fr,
        ports: PortTransform::Msb,
    },
    Alternative {
        implementation: "arkworks-msb/poly.append_point",
        contract: "poly.append_point",
        primary: Identity::Bls12381Fr,
        ports: PortTransform::Msb,
    },
];
