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
    Contract::selectable(
        "transcript.native.indexed.observe.bool",
        (
            &[Transcript, Bool, Indices],
            &[Transcript],
            AttributeRule::NativeMessageTemplate,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.native.indexed.observe.field",
        (
            &[Transcript, Field, Indices],
            &[Transcript],
            AttributeRule::NativeMessageTemplate,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.native.indexed.observe.group",
        (
            &[Transcript, Group, Indices],
            &[Transcript],
            AttributeRule::NativeMessageTemplate,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.native.indexed.observe.commitment",
        (
            &[Transcript, Commitment, Indices],
            &[Transcript],
            AttributeRule::NativeMessageTemplate,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.native.indexed.observe.proof",
        (
            &[Transcript, Proof, Indices],
            &[Transcript],
            AttributeRule::NativeMessageTemplate,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.native.indexed.observe.index",
        (
            &[Transcript, Index, Indices],
            &[Transcript],
            AttributeRule::NativeMessageTemplate,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.native.indexed.observe.field_array",
        (
            &[Transcript, FieldArray, Indices],
            &[Transcript],
            AttributeRule::NativeMessageTemplate,
        ),
    )
    .history(),
    Contract::new(
        "transcript.native.challenge",
        (
            &[Transcript],
            &[Field, Transcript],
            AttributeRule::NativeChallengeOrigin,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.native.observe.bool",
        (
            &[Transcript, Bool],
            &[Transcript],
            AttributeRule::NativeMessageOrigin,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.native.observe.field",
        (
            &[Transcript, Field],
            &[Transcript],
            AttributeRule::NativeMessageOrigin,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.native.observe.group",
        (
            &[Transcript, Group],
            &[Transcript],
            AttributeRule::NativeMessageOrigin,
        ),
    )
    .history(),
    Contract::new(
        "transcript.challenge",
        (
            &[Transcript],
            &[Field, Transcript],
            AttributeRule::ChallengeOrigin,
        ),
    )
    .history(),
    Contract::new(
        "transcript.draw_index",
        (
            &[Transcript, Index],
            &[Index, Transcript],
            AttributeRule::ChallengeOrigin,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.observe.bool",
        (
            &[Transcript, Bool],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.observe.index",
        (
            &[Transcript, Index],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.observe.indices",
        (
            &[Transcript, Indices],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.observe.field",
        (
            &[Transcript, Field],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.observe.matrix",
        (
            &[Transcript, Matrix],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.observe.vector",
        (
            &[Transcript, Vector],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.observe.polynomial",
        (
            &[Transcript, Polynomial],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.observe.round",
        (
            &[Transcript, Round],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.observe.table",
        (
            &[Transcript, Table],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.observe.point",
        (
            &[Transcript, Point],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.observe.group",
        (
            &[Transcript, Group],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.observe.groups",
        (
            &[Transcript, Groups],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.observe.commitment",
        (
            &[Transcript, Commitment],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.observe.proof",
        (
            &[Transcript, Proof],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    )
    .history(),
    Contract::selectable(
        "transcript.observe.commitments",
        (
            &[Transcript, Commitments],
            &[Transcript],
            AttributeRule::MessageOrigin,
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
    logical_refusals: &[],
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
    let challenge = matches!(
        binding.contract.as_str(),
        "transcript.challenge"
            | "transcript.draw_index"
            | "transcript.native.challenge"
            | "transcript.native.indexed.challenge"
    );
    let payload = if challenge {
        if binding.arguments.len() != 1 {
            return Err(support::failure());
        }
        if primary.transcript() != Some(primary) {
            return Err(support::failure());
        }
        None
    } else {
        if primary.transcript() != Some(primary) {
            return Err(support::failure());
        }
        let kind = *shape.inputs.get(1).ok_or_else(support::failure)?;
        let domain_free = matches!(kind, Bool | Index | Indices);
        let identity = if domain_free {
            Identity::None
        } else {
            Identity::parse(binding.arguments.get(1).ok_or_else(support::failure)?)?
        };
        let ty = if kind == FieldArray {
            if binding.arguments.len() != 3 {
                return Err(support::failure());
            }
            LogicalType::field_array(
                identity,
                crate::logical::natural_index(&binding.arguments[2])
                    .map_err(|_| support::failure())?,
            )?
        } else {
            let ty = LogicalType::new(kind, identity)?;
            if binding.arguments.len() != if domain_free { 2 } else { 3 }
                || binding.arguments.last() != ty.codec().as_ref()
            {
                return Err(support::failure());
            }
            ty
        };
        Some(ty)
    };
    if binding.contract == "transcript.draw_index" && primary != Identity::Merlin3KoalaBearExt8 {
        return Err(support::failure());
    }
    support::instantiate(shape, field, |kind| {
        if let Some(payload) = payload.as_ref().filter(|p| p.kind() == kind) {
            return Ok(payload.clone());
        }
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
    let primary = support::primary(binding)?;
    let field = primary.scalar_field().ok_or_else(support::failure)?;
    // Older per-kind observation operations retain their original profile.
    // The complete-type operation selects its codec independently of the suite.
    if binding.contract.starts_with("transcript.native.indexed.")
        && !matches!(
            binding.contract.as_str(),
            "transcript.native.indexed.challenge" | "transcript.native.indexed.observe.data"
        )
        && field != Identity::Bls12381Fr
    {
        return Err(support::failure());
    }

    if !matches!(
        binding.contract.as_str(),
        "transcript.native.indexed.observe.data"
            | "transcript.challenge"
            | "transcript.draw_index"
            | "transcript.native.challenge"
            | "transcript.native.indexed.challenge"
    ) {
        let payload = logical.inputs.get(1).ok_or_else(support::failure)?;
        let identity = payload
            .field_array_parts()
            .map_or(payload.identity(), |(field, _)| field);
        // The extension suite admits its base field and row commitments too.
        let supported = if primary == Identity::Merlin3KoalaBearExt8 {
            matches!(
                identity,
                Identity::KoalaBear
                    | Identity::KoalaBearExt8
                    | Identity::MerkleKoalaBear
                    | Identity::MerkleKoalaBearExt8
            )
        } else {
            identity.scalar_field() == Some(field)
        };
        if identity != Identity::None && !supported {
            return Err(support::failure());
        }
    }
    support::select_nominal(binding, logical, selection)
}
