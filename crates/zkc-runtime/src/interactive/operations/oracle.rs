//! Independently authored oracle operation contracts and physical policy.
use super::*;
use Type::*;

pub(super) const CONTRACTS: &[Contract] = &[
    Contract::new(
        "oracle.commit",
        (
            &[Vector, Index],
            &[Commitment, OpeningState],
            AttributeRule::None,
        ),
    )
    .implemented_by(&["plonky3/oracle.commit"]),
    Contract::new(
        "oracle.open",
        (
            &[OpeningState, Index],
            &[Vector, Proof],
            AttributeRule::None,
        ),
    )
    .implemented_by(&["plonky3/oracle.open"]),
    Contract::new(
        "oracle.check",
        (
            &[Commitment, Index, Index, Index, Vector, Proof],
            &[Bool],
            AttributeRule::None,
        ),
    )
    .implemented_by(&["plonky3/oracle.check"]),
    Contract::new(
        "commitments.empty",
        (&[], &[Commitments], AttributeRule::None),
    )
    .implemented_by(&["plonky3/commitments.empty"]),
    Contract::new(
        "commitments.append",
        (
            &[Commitments, Commitment],
            &[Commitments],
            AttributeRule::None,
        ),
    )
    .implemented_by(&["plonky3/commitments.append"]),
    Contract::new(
        "commitments.at",
        (&[Commitments, Index], &[Commitment], AttributeRule::None),
    )
    .implemented_by(&["plonky3/commitments.at"]),
    Contract::new(
        "commitments.length",
        (&[Commitments], &[Index], AttributeRule::None),
    )
    .implemented_by(&["plonky3/commitments.length"]),
    Contract::new(
        "opening_states.empty",
        (&[], &[OpeningStates], AttributeRule::None),
    )
    .implemented_by(&["plonky3/opening_states.empty"]),
    Contract::new(
        "opening_states.append",
        (
            &[OpeningStates, OpeningState],
            &[OpeningStates],
            AttributeRule::None,
        ),
    )
    .implemented_by(&["plonky3/opening_states.append"]),
    Contract::new(
        "opening_states.at",
        (
            &[OpeningStates, Index],
            &[OpeningState],
            AttributeRule::None,
        ),
    )
    .implemented_by(&["plonky3/opening_states.at"]),
    Contract::new(
        "opening_states.length",
        (&[OpeningStates], &[Index], AttributeRule::None),
    )
    .implemented_by(&["plonky3/opening_states.length"]),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled operation binding",
    physical_only: false,

    contracts: CONTRACTS,
    resolve,
    select: default_ports,
};

pub(super) fn resolve(
    binding: &OperationBinding,
    contract: &Contract,
) -> Result<KernelSignature<LogicalType>> {
    let fail = || AdmissionError::new(ErrorCode::Signature, "uninstalled operation binding");
    let shape = contract.shape()?;
    if binding.arguments.len() != 1 {
        return Err(fail());
    }
    let scheme = Identity::parse(&binding.arguments[0])?;
    if !scheme.is_row_commitment() {
        return Err(fail());
    }
    let make = |kind| {
        let identity = match kind {
            Type::Bool | Type::Index => Identity::None,
            Type::Vector => scheme.scalar_field().ok_or_else(fail)?,
            Type::Commitment
            | Type::OpeningState
            | Type::Proof
            | Type::Commitments
            | Type::OpeningStates => scheme,
            _ => return Err(fail()),
        };
        LogicalType::new(kind, identity)
    };
    Ok(KernelSignature {
        inputs: shape.inputs.into_iter().map(make).collect::<Result<_>>()?,
        outputs: shape.outputs.into_iter().map(make).collect::<Result<_>>()?,
        attributes: shape.attributes,
    })
}
