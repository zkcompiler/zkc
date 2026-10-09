//! Independently authored curve operation contracts and physical policy.
use super::*;
use Type::*;

pub(super) const CONTRACTS: &[Contract] = &[
    Contract::selectable("curve.neg", (&[Group], &[Group], AttributeRule::None))
        .implemented_by(&["arkworks/curve.neg", "dalek/curve.neg"]),
    Contract::selectable(
        "curve.nonidentity",
        (&[Group], &[Bool], AttributeRule::None),
    )
    .implemented_by(&["arkworks/curve.nonidentity", "dalek/curve.nonidentity"]),
    Contract::selectable(
        "curve.msm",
        (&[Vector, Groups], &[Group], AttributeRule::None),
    )
    .implemented_by(&["arkworks/curve.msm", "dalek/curve.msm"]),
    Contract::selectable(
        "curve.scale_each",
        (&[Vector, Groups], &[Groups], AttributeRule::None),
    )
    .implemented_by(&["arkworks/curve.scale_each", "dalek/curve.scale_each"]),
    Contract::selectable(
        "curve.vector_add",
        (&[Groups, Groups], &[Groups], AttributeRule::None),
    )
    .implemented_by(&["arkworks/curve.vector_add", "dalek/curve.vector_add"]),
    Contract::selectable(
        "curve.concat",
        (&[Groups, Groups], &[Groups], AttributeRule::None),
    )
    .implemented_by(&["arkworks/curve.concat", "dalek/curve.concat"]),
    Contract::selectable(
        "curve.vector_scale",
        (&[Groups, Field], &[Groups], AttributeRule::None),
    )
    .implemented_by(&["arkworks/curve.vector_scale", "dalek/curve.vector_scale"]),
    Contract::selectable(
        "curve.split",
        (&[Groups], &[Groups, Groups], AttributeRule::None),
    )
    .implemented_by(&["arkworks/curve.split", "dalek/curve.split"]),
    Contract::new(
        "pairing.apply",
        (&[Group, Group], &[Group], AttributeRule::None),
    )
    .implemented_by(&["arkworks/pairing.apply"]),
    Contract::new(
        "pairing.check",
        (&[Groups, Groups], &[Bool], AttributeRule::None),
    )
    .implemented_by(&["arkworks/pairing.check"]),
    Contract::selectable("curve.generator", (&[], &[Group], AttributeRule::None))
        .implemented_by(&["arkworks/curve.generator", "dalek/curve.generator"]),
    Contract::selectable(
        "curve.add",
        (&[Group, Group], &[Group], AttributeRule::None),
    )
    .implemented_by(&["arkworks/curve.add", "dalek/curve.add"]),
    Contract::selectable(
        "curve.scale",
        (&[Group, Field], &[Group], AttributeRule::None),
    )
    .implemented_by(&["arkworks/curve.scale", "dalek/curve.scale"]),
    Contract::selectable(
        "curve.equal",
        (&[Group, Group], &[Bool], AttributeRule::None),
    )
    .implemented_by(&["arkworks/curve.equal", "dalek/curve.equal"]),
    Contract::selectable("curve.empty", (&[], &[Groups], AttributeRule::None))
        .implemented_by(&["arkworks/curve.empty", "dalek/curve.empty"]),
    Contract::selectable(
        "curve.append",
        (&[Groups, Group], &[Groups], AttributeRule::None),
    )
    .implemented_by(&["arkworks/curve.append", "dalek/curve.append"]),
    Contract::selectable(
        "curve.at",
        (&[Groups], &[Group], AttributeRule::NaturalIndex),
    )
    .implemented_by(&["arkworks/curve.at", "dalek/curve.at"]),
    Contract::selectable(
        "curve.get",
        (&[Groups, Index], &[Group], AttributeRule::None),
    )
    .implemented_by(&["arkworks/curve.get", "dalek/curve.get"]),
    Contract::selectable("curve.length", (&[Groups], &[Index], AttributeRule::None))
        .implemented_by(&["arkworks/curve.length", "dalek/curve.length"]),
    Contract::selectable(
        "curve.commit",
        (&[Groups, Nonce], &[Groups, Nonce], AttributeRule::None),
    )
    .implemented_by(&["arkworks/curve.commit", "dalek/curve.commit"]),
    Contract::selectable(
        "curve.response",
        (&[Field, Field, Nonce], &[Field], AttributeRule::None),
    )
    .implemented_by(&["arkworks/curve.response", "dalek/curve.response"]),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: ALTERNATIVES,
    physical_error: "uninstalled operation binding",
    physical_only: false,

    contracts: CONTRACTS,
    resolve,
    select,
};

fn resolve(
    binding: &OperationBinding,
    contract: &Contract,
) -> Result<KernelSignature<LogicalType>> {
    let fail = || AdmissionError::new(ErrorCode::Signature, "uninstalled operation binding");
    if matches!(binding.contract.as_str(), "pairing.check" | "pairing.apply") {
        if binding.arguments != ["bn254.fr"] {
            return Err(fail());
        }
        let apply = binding.contract == "pairing.apply";
        let kind = if apply { Type::Group } else { Type::Groups };
        let make = LogicalType::new;
        return Ok(KernelSignature {
            inputs: vec![
                make(kind, Identity::Bn254G1)?,
                make(kind, Identity::Bn254G2)?,
            ],
            outputs: vec![if apply {
                make(Type::Group, Identity::Bn254Gt)?
            } else {
                make(Type::Bool, Identity::None)?
            }],
            attributes: AttributeRule::None,
        });
    }
    let shape = contract.shape()?;
    let primary = support::primary(binding)?;
    let field = primary.scalar_field().ok_or_else(fail)?;
    if binding.arguments.len() != 1 {
        return Err(fail());
    }
    let required = if binding.contract == "curve.response" {
        field
    } else {
        primary.group().ok_or_else(fail)?
    };
    if primary != required {
        return Err(fail());
    }
    support::instantiate(shape, field, |kind| match kind {
        Group | Groups => LogicalType::new(kind, primary.group().ok_or_else(fail)?),
        _ => support::field_type(kind, field),
    })
}

fn select(
    binding: &OperationBinding,
    logical: &KernelSignature<LogicalType>,
    selection: Selection,
) -> Result<BoundSignature> {
    if matches!(binding.contract.as_str(), "pairing.check" | "pairing.apply") {
        if binding.implementation != format!("arkworks/{}", binding.contract) {
            return Err(AdmissionError::new(
                ErrorCode::Signature,
                "uninstalled operation binding",
            ));
        }
        default_ports(binding, logical, selection)
    } else {
        support::select_nominal(binding, logical, selection)
    }
}

use super::super::Representation;
use super::super::domain_bindings::PortTransform;
const ALTERNATIVES: &[Alternative] = &[
    Alternative {
        implementation: "dalek-diagonal/curve.scale_each",
        contract: "curve.scale_each",
        primary: Identity::Ristretto255Group,
        ports: PortTransform::Diagonal {
            output: true,
            port: 0,
            representation: Representation::RistrettoDiagonal,
        },
    },
    Alternative {
        implementation: "dalek-diagonal/curve.msm",
        contract: "curve.msm",
        primary: Identity::Ristretto255Group,
        ports: PortTransform::Diagonal {
            output: false,
            port: 1,
            representation: Representation::RistrettoDiagonal,
        },
    },
];
