//! Independently authored curve operation contracts and physical policy.
use super::*;
use Type::*;

pub(super) const CONTRACTS: &[Contract] = &[
    Contract::selectable("curve.neg", (&[Group], &[Group], AttributeRule::None)),
    Contract::selectable(
        "curve.nonidentity",
        (&[Group], &[Bool], AttributeRule::None),
    ),
    Contract::selectable(
        "curve.msm",
        (&[Vector, Groups], &[Group], AttributeRule::None),
    ),
    Contract::selectable(
        "curve.scale_each",
        (&[Vector, Groups], &[Groups], AttributeRule::None),
    ),
    Contract::selectable(
        "curve.vector_add",
        (&[Groups, Groups], &[Groups], AttributeRule::None),
    ),
    Contract::selectable(
        "curve.concat",
        (&[Groups, Groups], &[Groups], AttributeRule::None),
    ),
    Contract::selectable(
        "curve.vector_scale",
        (&[Groups, Field], &[Groups], AttributeRule::None),
    ),
    Contract::selectable(
        "curve.split",
        (&[Groups], &[Groups, Groups], AttributeRule::None),
    ),
    Contract::new(
        "pairing.check",
        (&[Groups, Groups], &[Bool], AttributeRule::None),
    ),
    Contract::selectable("curve.generator", (&[], &[Group], AttributeRule::None)),
    Contract::selectable(
        "curve.add",
        (&[Group, Group], &[Group], AttributeRule::None),
    ),
    Contract::selectable(
        "curve.scale",
        (&[Group, Field], &[Group], AttributeRule::None),
    ),
    Contract::selectable(
        "curve.equal",
        (&[Group, Group], &[Bool], AttributeRule::None),
    ),
    Contract::selectable("curve.empty", (&[], &[Groups], AttributeRule::None)),
    Contract::selectable(
        "curve.append",
        (&[Groups, Group], &[Groups], AttributeRule::None),
    ),
    Contract::selectable(
        "curve.at",
        (&[Groups], &[Group], AttributeRule::NaturalIndex),
    ),
    Contract::selectable(
        "curve.get",
        (&[Groups, Index], &[Group], AttributeRule::None),
    ),
    Contract::selectable("curve.length", (&[Groups], &[Index], AttributeRule::None)),
    Contract::selectable(
        "curve.commit",
        (&[Groups, Nonce], &[Groups, Nonce], AttributeRule::None),
    ),
    Contract::selectable(
        "curve.response",
        (&[Field, Field, Nonce], &[Field], AttributeRule::None),
    ),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: ALTERNATIVES,
    logical_refusals: &[],
    physical_error: "uninstalled operation binding",
    physical_only: false,

    contracts: CONTRACTS,
    resolve,
    providers: &["arkworks", "dalek"],
    select,
};

fn resolve(
    binding: &OperationBinding,
    contract: &Contract,
) -> Result<KernelSignature<LogicalType>> {
    let fail = || AdmissionError::new(ErrorCode::Signature, "uninstalled operation binding");
    if binding.contract == "pairing.check" {
        if binding.arguments != ["bn254.fr"] {
            return Err(fail());
        }
        let make = LogicalType::new;
        return Ok(KernelSignature {
            inputs: vec![
                make(Type::Groups, Identity::Bn254G1)?,
                make(Type::Groups, Identity::Bn254G2)?,
            ],
            outputs: vec![make(Type::Bool, Identity::None)?],
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
    if binding.contract == "pairing.check" {
        if binding.implementation != "arkworks/pairing.check" {
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
    Alternative {
        implementation: "dalek-vartime/curve.msm",
        contract: "curve.msm",
        primary: Identity::Ristretto255Group,
        ports: PortTransform::Default,
    },
];
