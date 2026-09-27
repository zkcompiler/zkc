//! Independently authored transcript contracts and admission.
use super::*;
use Type::*;

pub(super) const CONTRACTS: &[Contract] = &[
    Contract::new(
        "transcript.challenge",
        (
            &[Transcript],
            &[Field, Transcript],
            AttributeRule::ChallengeOrigin,
        ),
    ),
    Contract::new(
        "transcript.draw_index",
        (
            &[Transcript, Index],
            &[Index, Transcript],
            AttributeRule::ChallengeOrigin,
        ),
    ),
    Contract::selectable(
        "transcript.observe.bool",
        (
            &[Transcript, Bool],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    ),
    Contract::selectable(
        "transcript.observe.index",
        (
            &[Transcript, Index],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    ),
    Contract::selectable(
        "transcript.observe.indices",
        (
            &[Transcript, Indices],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    ),
    Contract::selectable(
        "transcript.observe.field",
        (
            &[Transcript, Field],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    ),
    Contract::selectable(
        "transcript.observe.matrix",
        (
            &[Transcript, Matrix],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    ),
    Contract::selectable(
        "transcript.observe.vector",
        (
            &[Transcript, Vector],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    ),
    Contract::selectable(
        "transcript.observe.polynomial",
        (
            &[Transcript, Polynomial],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    ),
    Contract::selectable(
        "transcript.observe.round",
        (
            &[Transcript, Round],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    ),
    Contract::selectable(
        "transcript.observe.table",
        (
            &[Transcript, Table],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    ),
    Contract::selectable(
        "transcript.observe.point",
        (
            &[Transcript, Point],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    ),
    Contract::selectable(
        "transcript.observe.group",
        (
            &[Transcript, Group],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    ),
    Contract::selectable(
        "transcript.observe.groups",
        (
            &[Transcript, Groups],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    ),
    Contract::selectable(
        "transcript.observe.commitment",
        (
            &[Transcript, Commitment],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    ),
    Contract::selectable(
        "transcript.observe.proof",
        (
            &[Transcript, Proof],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    ),
    Contract::selectable(
        "transcript.observe.commitments",
        (
            &[Transcript, Commitments],
            &[Transcript],
            AttributeRule::MessageOrigin,
        ),
    ),
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
    let shape = contract.shape()?;
    let primary = support::primary(binding)?;
    let field = primary.scalar_field().ok_or_else(support::failure)?;
    let challenge = matches!(
        binding.contract.as_str(),
        "transcript.challenge" | "transcript.draw_index"
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
        let ty = LogicalType::new(kind, identity)?;
        if binding.arguments.len() != if domain_free { 2 } else { 3 }
            || binding.arguments.last() != ty.codec().as_ref()
        {
            return Err(support::failure());
        }
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
    if !matches!(
        binding.contract.as_str(),
        "transcript.challenge" | "transcript.draw_index"
    ) {
        let identity = logical
            .inputs
            .get(1)
            .ok_or_else(support::failure)?
            .identity();
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
