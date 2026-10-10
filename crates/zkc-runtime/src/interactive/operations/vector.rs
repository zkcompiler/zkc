//! Independently authored vector operation contracts and physical policy.
use super::*;
use Type::*;

pub(super) const CONTRACTS: &[Contract] = &[
    Contract::selectable(
        "vector.get",
        (&[Vector, Index], &[Field], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/vector.get",
        "dalek/vector.get",
        "plonky3/vector.get",
    ]),
    Contract::selectable(
        "vector.slice",
        (&[Vector, Index, Index], &[Vector], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/vector.slice",
        "dalek/vector.slice",
        "plonky3/vector.slice",
    ]),
    Contract::selectable(
        "vector.transpose",
        (&[Vector, Index, Index], &[Vector], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/vector.transpose",
        "dalek/vector.transpose",
        "plonky3/vector.transpose",
    ]),
    Contract::selectable("vector.length", (&[Vector], &[Index], AttributeRule::None))
        .implemented_by(&[
            "arkworks/vector.length",
            "dalek/vector.length",
            "plonky3/vector.length",
        ]),
    Contract::selectable(
        "vector.rotate",
        (&[Vector, Index], &[Vector], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/vector.rotate",
        "dalek/vector.rotate",
        "plonky3/vector.rotate",
    ]),
    Contract::selectable(
        "vector.interleave",
        (&[Vector, Vector], &[Vector], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/vector.interleave",
        "dalek/vector.interleave",
        "plonky3/vector.interleave",
    ]),
    Contract::selectable(
        "vector.prefix_product",
        (&[Vector], &[Vector], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/vector.prefix_product",
        "dalek/vector.prefix_product",
        "plonky3/vector.prefix_product",
    ]),
    Contract::selectable(
        "vector.prefix_sum",
        (&[Vector], &[Vector], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/vector.prefix_sum",
        "dalek/vector.prefix_sum",
        "plonky3/vector.prefix_sum",
    ]),
    Contract::selectable(
        "vector.inverse",
        (&[Vector], &[Vector], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/vector.inverse",
        "dalek/vector.inverse",
        "plonky3/vector.inverse",
    ]),
    Contract::new("vector.embed", (&[Vector], &[Vector], AttributeRule::None))
        .implemented_by(&["plonky3/vector.embed"]),
    Contract::selectable(
        "vector.fill",
        (&[Field, Index], &[Vector], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/vector.fill",
        "dalek/vector.fill",
        "plonky3/vector.fill",
    ]),
    Contract::selectable(
        "vector.geometric",
        (&[Field, Index], &[Vector], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/vector.geometric",
        "dalek/vector.geometric",
        "plonky3/vector.geometric",
    ]),
    Contract::selectable(
        "vector.constant",
        (&[], &[Vector], AttributeRule::FieldDecimals),
    )
    .implemented_by(&[
        "arkworks/vector.constant",
        "dalek/vector.constant",
        "plonky3/vector.constant",
    ]),
    Contract::selectable(
        "vector.scatter_sum",
        (&[Vector], &[Vector], AttributeRule::ScatterShape),
    )
    .implemented_by(&[
        "arkworks/vector.scatter_sum",
        "dalek/vector.scatter_sum",
        "plonky3/vector.scatter_sum",
    ]),
    Contract::selectable("vector.empty", (&[], &[Vector], AttributeRule::None)).implemented_by(&[
        "arkworks/vector.empty",
        "dalek/vector.empty",
        "plonky3/vector.empty",
    ]),
    Contract::selectable(
        "vector.append",
        (&[Vector, Field], &[Vector], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/vector.append",
        "dalek/vector.append",
        "plonky3/vector.append",
    ]),
    Contract::selectable(
        "vector.splat",
        (&[Field], &[Vector], AttributeRule::NaturalIndex),
    )
    .implemented_by(&[
        "arkworks/vector.splat",
        "dalek/vector.splat",
        "plonky3/vector.splat",
    ]),
    Contract::selectable(
        "vector.powers",
        (&[Field], &[Vector], AttributeRule::NaturalIndex),
    )
    .implemented_by(&[
        "arkworks/vector.powers",
        "dalek/vector.powers",
        "plonky3/vector.powers",
    ]),
    Contract::selectable(
        "vector.equal",
        (&[Vector, Vector], &[Bool], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/vector.equal",
        "dalek/vector.equal",
        "plonky3/vector.equal",
    ]),
    Contract::selectable(
        "vector.add",
        (&[Vector, Vector], &[Vector], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/vector.add",
        "dalek/vector.add",
        "plonky3/vector.add",
    ]),
    Contract::selectable(
        "vector.sub",
        (&[Vector, Vector], &[Vector], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/vector.sub",
        "dalek/vector.sub",
        "plonky3/vector.sub",
    ]),
    Contract::selectable(
        "vector.mul",
        (&[Vector, Vector], &[Vector], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/vector.mul",
        "dalek/vector.mul",
        "plonky3/vector.mul",
    ]),
    Contract::selectable(
        "vector.concat",
        (&[Vector, Vector], &[Vector], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/vector.concat",
        "dalek/vector.concat",
        "plonky3/vector.concat",
    ]),
    Contract::selectable(
        "vector.kronecker",
        (&[Vector, Vector], &[Vector], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/vector.kronecker",
        "dalek/vector.kronecker",
        "plonky3/vector.kronecker",
    ]),
    Contract::selectable(
        "vector.scale",
        (&[Vector, Field], &[Vector], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/vector.scale",
        "dalek/vector.scale",
        "plonky3/vector.scale",
    ]),
    Contract::selectable("vector.sum", (&[Vector], &[Field], AttributeRule::None)).implemented_by(
        &[
            "arkworks/vector.sum",
            "dalek/vector.sum",
            "plonky3/vector.sum",
        ],
    ),
    Contract::selectable(
        "vector.dot",
        (&[Vector, Vector], &[Field], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/vector.dot",
        "dalek/vector.dot",
        "plonky3/vector.dot",
    ]),
    Contract::selectable(
        "vector.split",
        (&[Vector], &[Vector, Vector], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/vector.split",
        "dalek/vector.split",
        "plonky3/vector.split",
    ]),
    Contract::selectable(
        "vector.at",
        (&[Vector], &[Field], AttributeRule::NaturalIndex),
    )
    .implemented_by(&["arkworks/vector.at", "dalek/vector.at", "plonky3/vector.at"]),
    Contract::selectable(
        "vector.length_check",
        (&[Vector], &[Bool], AttributeRule::NaturalIndex),
    )
    .implemented_by(&[
        "arkworks/vector.length_check",
        "dalek/vector.length_check",
        "plonky3/vector.length_check",
    ]),
    Contract::selectable(
        "vector.gather",
        (&[Vector], &[Vector], AttributeRule::NaturalIndices),
    )
    .implemented_by(&[
        "arkworks/vector.gather",
        "dalek/vector.gather",
        "plonky3/vector.gather",
    ]),
    Contract::selectable(
        "vector.matvec",
        (&[Vector, Vector], &[Vector], AttributeRule::MatrixShape),
    )
    .implemented_by(&[
        "arkworks/vector.matvec",
        "dalek/vector.matvec",
        "plonky3/vector.matvec",
    ]),
    Contract::selectable(
        "vector.from_point",
        (&[Point], &[Vector], AttributeRule::None),
    )
    .implemented_by(&["arkworks/vector.from_point"]),
    Contract::selectable(
        "vector.to_point",
        (&[Vector], &[Point], AttributeRule::None),
    )
    .implemented_by(&["arkworks/vector.to_point"]),
    Contract::selectable(
        "vector.from_table",
        (&[Table], &[Vector], AttributeRule::None),
    )
    .implemented_by(&["arkworks/vector.from_table"]),
    Contract::selectable(
        "vector.to_table",
        (&[Vector], &[Table], AttributeRule::None),
    )
    .implemented_by(&["arkworks/vector.to_table"]),
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
