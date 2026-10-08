//! Independently authored vector operation contracts and physical policy.
use super::*;
use Type::*;

pub(super) const CONTRACTS: &[Contract] = &[
    Contract::selectable(
        "vector.get",
        (&[Vector, Index], &[Field], AttributeRule::None),
    ),
    Contract::selectable(
        "vector.slice",
        (&[Vector, Index, Index], &[Vector], AttributeRule::None),
    ),
    Contract::selectable("vector.length", (&[Vector], &[Index], AttributeRule::None)),
    Contract::selectable(
        "vector.rotate",
        (&[Vector, Index], &[Vector], AttributeRule::None),
    ),
    Contract::selectable(
        "vector.interleave",
        (&[Vector, Vector], &[Vector], AttributeRule::None),
    ),
    Contract::selectable(
        "vector.prefix_product",
        (&[Vector], &[Vector], AttributeRule::None),
    ),
    Contract::selectable(
        "vector.prefix_sum",
        (&[Vector], &[Vector], AttributeRule::None),
    ),
    Contract::selectable(
        "vector.inverse",
        (&[Vector], &[Vector], AttributeRule::None),
    ),
    Contract::new("vector.embed", (&[Vector], &[Vector], AttributeRule::None)),
    Contract::selectable(
        "vector.fill",
        (&[Field, Index], &[Vector], AttributeRule::None),
    ),
    Contract::selectable(
        "vector.geometric",
        (&[Field, Index], &[Vector], AttributeRule::None),
    ),
    Contract::selectable(
        "vector.constant",
        (&[], &[Vector], AttributeRule::FieldDecimals),
    ),
    Contract::selectable(
        "vector.scatter_sum",
        (&[Vector], &[Vector], AttributeRule::ScatterShape),
    ),
    Contract::selectable("vector.empty", (&[], &[Vector], AttributeRule::None)),
    Contract::selectable(
        "vector.append",
        (&[Vector, Field], &[Vector], AttributeRule::None),
    ),
    Contract::selectable(
        "vector.splat",
        (&[Field], &[Vector], AttributeRule::NaturalIndex),
    ),
    Contract::selectable(
        "vector.powers",
        (&[Field], &[Vector], AttributeRule::NaturalIndex),
    ),
    Contract::selectable(
        "vector.equal",
        (&[Vector, Vector], &[Bool], AttributeRule::None),
    ),
    Contract::selectable(
        "vector.add",
        (&[Vector, Vector], &[Vector], AttributeRule::None),
    ),
    Contract::selectable(
        "vector.sub",
        (&[Vector, Vector], &[Vector], AttributeRule::None),
    ),
    Contract::selectable(
        "vector.mul",
        (&[Vector, Vector], &[Vector], AttributeRule::None),
    ),
    Contract::selectable(
        "vector.concat",
        (&[Vector, Vector], &[Vector], AttributeRule::None),
    ),
    Contract::selectable(
        "vector.kronecker",
        (&[Vector, Vector], &[Vector], AttributeRule::None),
    ),
    Contract::selectable(
        "vector.scale",
        (&[Vector, Field], &[Vector], AttributeRule::None),
    ),
    Contract::selectable("vector.sum", (&[Vector], &[Field], AttributeRule::None)),
    Contract::selectable(
        "vector.dot",
        (&[Vector, Vector], &[Field], AttributeRule::None),
    ),
    Contract::selectable(
        "vector.split",
        (&[Vector], &[Vector, Vector], AttributeRule::None),
    ),
    Contract::selectable(
        "vector.at",
        (&[Vector], &[Field], AttributeRule::NaturalIndex),
    ),
    Contract::selectable(
        "vector.length_check",
        (&[Vector], &[Bool], AttributeRule::NaturalIndex),
    ),
    Contract::selectable(
        "vector.gather",
        (&[Vector], &[Vector], AttributeRule::NaturalIndices),
    ),
    Contract::selectable(
        "vector.matvec",
        (&[Vector, Vector], &[Vector], AttributeRule::MatrixShape),
    ),
    Contract::selectable(
        "vector.from_point",
        (&[Point], &[Vector], AttributeRule::None),
    ),
    Contract::selectable(
        "vector.to_point",
        (&[Vector], &[Point], AttributeRule::None),
    ),
    Contract::selectable(
        "vector.from_table",
        (&[Table], &[Vector], AttributeRule::None),
    ),
    Contract::selectable(
        "vector.to_table",
        (&[Vector], &[Table], AttributeRule::None),
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
    let mut signature = support::field_signature(binding, contract)?;
    if binding.contract == "vector.embed" {
        let base = support::primary(binding)?
            .base_field()
            .ok_or_else(support::failure)?;
        *signature.inputs.first_mut().ok_or_else(support::failure)? =
            LogicalType::new(Vector, base)?;
    }
    Ok(signature)
}

use super::super::Representation;
use super::super::domain_bindings::PortTransform;
const ALTERNATIVES: &[Alternative] = &[
    Alternative {
        implementation: "arkworks-msb/vector.from_table",
        contract: "vector.from_table",
        primary: Identity::Bls12381Fr,
        ports: PortTransform::Msb,
    },
    Alternative {
        implementation: "arkworks-msb/vector.to_table",
        contract: "vector.to_table",
        primary: Identity::Bls12381Fr,
        ports: PortTransform::Msb,
    },
    Alternative {
        implementation: "arkworks-diagonal/vector.mul",
        contract: "vector.mul",
        primary: Identity::Bls12381Fr,
        ports: PortTransform::Diagonal {
            output: true,
            port: 0,
            representation: Representation::FrDiagonal,
        },
    },
    Alternative {
        implementation: "arkworks-diagonal/vector.dot",
        contract: "vector.dot",
        primary: Identity::Bls12381Fr,
        ports: PortTransform::Diagonal {
            output: false,
            port: 1,
            representation: Representation::FrDiagonal,
        },
    },
    Alternative {
        implementation: "arkworks-pairwise/vector.dot",
        contract: "vector.dot",
        primary: Identity::Bls12381Fr,
        ports: PortTransform::Default,
    },
];
