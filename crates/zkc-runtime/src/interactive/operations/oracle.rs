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
    ),
    Contract::new(
        "oracle.open",
        (
            &[OpeningState, Index],
            &[Vector, Proof],
            AttributeRule::None,
        ),
    ),
    Contract::new(
        "oracle.check",
        (
            &[Commitment, Index, Index, Index, Vector, Proof],
            &[Bool],
            AttributeRule::None,
        ),
    ),
    Contract::new(
        "commitments.empty",
        (&[], &[Commitments], AttributeRule::None),
    ),
    Contract::new(
        "commitments.append",
        (
            &[Commitments, Commitment],
            &[Commitments],
            AttributeRule::None,
        ),
    ),
    Contract::new(
        "commitments.at",
        (&[Commitments, Index], &[Commitment], AttributeRule::None),
    ),
    Contract::new(
        "commitments.length",
        (&[Commitments], &[Index], AttributeRule::None),
    ),
    Contract::new(
        "opening_states.empty",
        (&[], &[OpeningStates], AttributeRule::None),
    ),
    Contract::new(
        "opening_states.append",
        (
            &[OpeningStates, OpeningState],
            &[OpeningStates],
            AttributeRule::None,
        ),
    ),
    Contract::new(
        "opening_states.at",
        (
            &[OpeningStates, Index],
            &[OpeningState],
            AttributeRule::None,
        ),
    ),
    Contract::new(
        "opening_states.length",
        (&[OpeningStates], &[Index], AttributeRule::None),
    ),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    logical_refusals: &[],
    physical_error: "uninstalled operation binding",
    physical_only: false,

    contracts: CONTRACTS,
    resolve,
    providers: &["plonky3"],
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
