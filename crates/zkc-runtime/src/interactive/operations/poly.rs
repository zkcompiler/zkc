//! Independently authored poly operation contracts and physical policy.
use super::*;
use Type::*;

pub(super) const CONTRACTS: &[Contract] = &[
    Contract::selectable(
        "poly.table_arity",
        (&[Table], &[Index], AttributeRule::None),
    ),
    Contract::selectable(
        "poly.coefficient_count",
        (&[Polynomial], &[Index], AttributeRule::None),
    ),
    Contract::selectable(
        "poly.coset_evaluate",
        (&[Polynomial, Field, Index], &[Vector], AttributeRule::None),
    ),
    Contract::selectable(
        "poly.coset_interpolate",
        (&[Vector, Field], &[Polynomial], AttributeRule::None),
    ),
    Contract::selectable(
        "poly.domain_point",
        (&[Field, Index, Index], &[Field], AttributeRule::None),
    ),
    Contract::selectable(
        "poly.domain_root",
        (&[Index], &[Field], AttributeRule::None),
    ),
    Contract::selectable(
        "poly.domain_points",
        (&[Field, Index], &[Vector], AttributeRule::None),
    ),
    Contract::selectable(
        "poly.even_odd_fold",
        (&[Vector, Field, Field], &[Vector], AttributeRule::None),
    ),
    Contract::selectable(
        "poly.divide_opening",
        (
            &[Polynomial, Field, Field],
            &[Polynomial],
            AttributeRule::None,
        ),
    ),
    Contract::selectable(
        "poly.opening_quotient",
        (
            &[Vector, Field, Field, Field],
            &[Vector],
            AttributeRule::None,
        ),
    ),
    Contract::selectable(
        "poly.equality_weights",
        (&[Point], &[Vector], AttributeRule::None),
    ),
    Contract::selectable(
        "poly.from_coefficients",
        (&[Vector], &[Polynomial], AttributeRule::None),
    ),
    Contract::selectable(
        "poly.coefficients",
        (&[Polynomial], &[Vector], AttributeRule::None),
    ),
    Contract::selectable(
        "poly.degree_check",
        (&[Polynomial], &[Bool], AttributeRule::NaturalIndex),
    ),
    Contract::selectable(
        "poly.univariate_evaluate",
        (&[Polynomial, Field], &[Field], AttributeRule::None),
    ),
    Contract::selectable(
        "poly.univariate_boundary",
        (&[Polynomial], &[Field], AttributeRule::None),
    ),
    Contract::selectable(
        "poly.product_sum",
        (&[Table, Table], &[Field], AttributeRule::None),
    ),
    Contract::selectable(
        "poly.product_round",
        (&[Table, Table], &[Round], AttributeRule::None),
    ),
    Contract::selectable("poly.boundary", (&[Round], &[Field], AttributeRule::None)),
    Contract::selectable(
        "poly.round_evaluate",
        (&[Round, Field], &[Field], AttributeRule::None),
    ),
    Contract::selectable(
        "poly.fold",
        (&[Table, Field], &[Table], AttributeRule::None),
    ),
    Contract::selectable(
        "poly.evaluate",
        (&[Table, Point], &[Field], AttributeRule::None),
    ),
    Contract::selectable("poly.empty_point", (&[], &[Point], AttributeRule::None)),
    Contract::selectable(
        "poly.append_point",
        (&[Point, Field], &[Point], AttributeRule::None),
    ),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: ALTERNATIVES,
    physical_error: "uninstalled operation binding",
    physical_only: false,

    contracts: CONTRACTS,
    resolve,
    providers: &["arkworks", "dalek", "plonky3"],
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
