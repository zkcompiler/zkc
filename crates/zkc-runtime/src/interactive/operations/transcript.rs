//! Independently authored transcript contracts and admission.
use super::*;
use Type::*;

pub(super) const CONTRACTS: &[Contract] = &[
    Contract {
        alternatives: true,
        ..Contract::custom("transcript.native.indexed.observe.data").history()
    },
    Contract::new(
        "transcript.native.indexed.challenge",
        (
            &[Transcript, Indices],
            &[Field, Transcript],
            AttributeRule::NativeChallengeTemplate,
        ),
    )
    .history(),
];

pub(super) const CONTRIBUTION: Contribution = Contribution {
    contracts: CONTRACTS,
    resolve,
    select,
    providers: &["arkworks", "dalek", "plonky3", "spongefish"],
    alternatives: &[],
    physical_error: "uninstalled operation binding",
    physical_only: false,
};

fn resolve(
    binding: &OperationBinding,
    contract: &Contract,
) -> Result<KernelSignature<LogicalType>> {
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
        return Ok(KernelSignature {
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
    support::instantiate(shape, field, |kind| {
        if kind == Transcript {
            LogicalType::new(kind, primary)
        } else if kind == Indices {
            LogicalType::new(kind, Identity::None)
        } else {
            support::field_type(kind, field)
        }
    })
}

fn select(
    binding: &OperationBinding,
    logical: &KernelSignature<LogicalType>,
    selection: Selection,
) -> Result<BoundSignature> {
    support::select_nominal(binding, logical, selection)
}
