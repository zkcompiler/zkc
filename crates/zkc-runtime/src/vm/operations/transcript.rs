//! Independently authored transcript contracts and admission.
use super::super::PhysicalType;
use super::*;
use Type::*;

pub(super) const CONTRACTS: &[Contract] = &[
    Contract::new(
        "transcript.observe",
        (
            &[Transcript, Bytes, Bytes],
            &[Transcript],
            AttributeRule::None,
        ),
    )
    .implemented_by(&[
        "arkworks/transcript.observe",
        "dalek/transcript.observe",
        "plonky3/transcript.observe",
        "spongefish/transcript.observe",
    ])
    .history(),
    Contract::new(
        "transcript.challenge",
        (
            &[Transcript, Bytes],
            &[Transcript, Field],
            AttributeRule::None,
        ),
    )
    .implemented_by(&[
        "arkworks/transcript.challenge",
        "dalek/transcript.challenge",
        "plonky3/transcript.challenge",
        "spongefish/transcript.challenge",
    ])
    .history(),
    Contract::new(
        "transcript.index",
        (
            &[Transcript, Bytes, Index],
            &[Transcript, Index],
            AttributeRule::None,
        ),
    )
    .implemented_by(&["plonky3/transcript.index"])
    .history(),
    Contract {
        alternatives: true,
        ..Contract::custom("transcript.native.indexed.observe.data")
            .implemented_by(&[
                "arkworks/transcript.native.indexed.observe.data",
                "dalek/transcript.native.indexed.observe.data",
                "plonky3/transcript.native.indexed.observe.data",
                "spongefish/transcript.native.indexed.observe.data",
            ])
            .history()
    },
    Contract::new(
        "transcript.native.indexed.challenge",
        (
            &[Transcript, Indices],
            &[Field, Transcript],
            AttributeRule::NativeChallengeTemplate,
        ),
    )
    .implemented_by(&[
        "arkworks/transcript.native.indexed.challenge",
        "dalek/transcript.native.indexed.challenge",
        "plonky3/transcript.native.indexed.challenge",
        "spongefish/transcript.native.indexed.challenge",
    ])
    .history(),
    Contract::new(
        "transcript.native.indexed.index",
        (
            &[Transcript, Index, Indices],
            &[Index, Transcript],
            AttributeRule::NativeIndexTemplate,
        ),
    )
    .implemented_by(&["plonky3/transcript.native.indexed.index"])
    .history(),
];

pub(super) const CONTRIBUTION: Contribution = Contribution {
    contracts: CONTRACTS,
    resolve,
    select,
    alternatives: &[],
    physical_error: "uninstalled operation binding",
    physical_only: false,
};

fn resolve(
    binding: &OperationBinding,
    contract: &Contract,
) -> Result<OperationSignature<LogicalType>> {
    if binding.contract == "transcript.native.indexed.observe.data" {
        if binding.arguments.len() != 2 {
            return Err(support::failure());
        }
        let primary = support::primary(binding)?;
        if primary.transcript() != Some(primary) {
            return Err(support::failure());
        }
        let payload = LogicalType::parse(&binding.arguments[1])?;
        if !payload.is_native_message_data() {
            return Err(support::failure());
        }
        let state = LogicalType::new(Transcript, primary)?;
        return Ok(OperationSignature {
            inputs: vec![
                state.clone(),
                payload,
                LogicalType::new(Indices, Identity::None)?,
            ],
            outputs: vec![state],
            attributes: AttributeRule::NativeMessageTemplate,
        });
    }
    let shape = contract.shape()?;
    let primary = support::primary(binding)?;
    let field = primary.scalar_field().ok_or_else(support::failure)?;
    if binding.arguments.len() != 1 || primary.transcript() != Some(primary) {
        return Err(support::failure());
    }
    // UniformIndex transitions exist only for suites whose challenge field
    // has index randomness; other suites' byte samplers are not installed.
    if matches!(
        binding.contract.as_str(),
        "transcript.native.indexed.index" | "transcript.index"
    ) && !primary.has_index_transcript()
    {
        return Err(support::failure());
    }
    support::instantiate(shape, field, |kind| {
        if kind == Transcript {
            LogicalType::new(kind, primary)
        } else if kind == Indices || kind == Bytes {
            LogicalType::new(kind, Identity::None)
        } else {
            support::field_type(kind, field)
        }
    })
}

fn select(
    binding: &OperationBinding,
    logical: &OperationSignature<LogicalType>,
    selection: Selection,
) -> Result<BoundSignature> {
    support::select_nominal(binding, logical, selection)
}

/// Only the canonical message payload is physically selectable. Resource and
/// coordinate ports, logical schema and exact suite owner retain their rules.
pub(super) fn select_payload(
    binding: &OperationBinding,
    logical: &OperationSignature<LogicalType>,
    selection: Selection,
    physical: &[PhysicalType],
) -> Result<BoundSignature> {
    let mut signature = select(binding, logical, selection)?;
    match physical {
        [] => {}
        [payload] if payload.logical() == &logical.inputs[1] => {
            signature.inputs[1] = payload.clone();
        }
        _ => return Err(support::failure()),
    }
    Ok(signature)
}
