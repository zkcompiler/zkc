//! Installed random operation implementations.
use super::*;

pub(super) const CONTRACTS: &[Installation] = &[
    Installation::new("random.vector").implemented_by(&[
        "arkworks/random.vector",
        "dalek/random.vector",
        "plonky3/random.vector",
    ]),
    Installation::new("random.index").implemented_by(&["plonky3/random.index"]),
    Installation::new("random.draw").implemented_by(&[
        "arkworks/random.draw",
        "dalek/random.draw",
        "plonky3/random.draw",
    ]),
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
    selection.require_default()?;
    support::select_nominal(binding, logical, selection)
}
