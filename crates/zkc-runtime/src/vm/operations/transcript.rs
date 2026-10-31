//! Installed transcript operation implementations.
use super::super::PhysicalType;
use super::*;

pub(super) const CONTRACTS: &[Installation] = &[
    Installation::new("transcript.observe").implemented_by(&[
        "arkworks/transcript.observe",
        "dalek/transcript.observe",
        "plonky3/transcript.observe",
        "spongefish/transcript.observe",
    ]),
    Installation::new("transcript.challenge").implemented_by(&[
        "arkworks/transcript.challenge",
        "dalek/transcript.challenge",
        "plonky3/transcript.challenge",
        "spongefish/transcript.challenge",
    ]),
    Installation::new("transcript.index").implemented_by(&["plonky3/transcript.index"]),
    Installation {
        alternatives: true,
        ..Installation::new("transcript.native.indexed.observe.data").implemented_by(&[
            "arkworks/transcript.native.indexed.observe.data",
            "dalek/transcript.native.indexed.observe.data",
            "plonky3/transcript.native.indexed.observe.data",
            "spongefish/transcript.native.indexed.observe.data",
        ])
    },
    Installation::new("transcript.native.indexed.challenge").implemented_by(&[
        "arkworks/transcript.native.indexed.challenge",
        "dalek/transcript.native.indexed.challenge",
        "plonky3/transcript.native.indexed.challenge",
        "spongefish/transcript.native.indexed.challenge",
    ]),
    Installation::new("transcript.native.indexed.index")
        .implemented_by(&["plonky3/transcript.native.indexed.index"]),
    Installation::new("transcript.native.indexed.indices")
        .implemented_by(&["plonky3/transcript.native.indexed.indices"]),
    Installation::new("transcript.native.indexed.indices.search")
        .implemented_by(&["plonky3/transcript.native.indexed.indices.search"]),
    Installation::new("transcript.native.indexed.indices.gated")
        .implemented_by(&["plonky3/transcript.native.indexed.indices.gated"]),
];

pub(super) const CONTRIBUTION: Contribution = Contribution {
    contracts: CONTRACTS,

    select,
    alternatives: &[],
    physical_error: "uninstalled operation binding",
};

fn select(
    binding: &OperationBinding,
    logical: &OperationSignature<LogicalType>,
    selection: Selection,
) -> Result<BoundSignature> {
    if binding
        .contract
        .starts_with("transcript.native.indexed.indices")
        && !support::primary(binding)?.has_index_block_transcript()
    {
        return Err(support::failure());
    }
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
