//! Independently authored pcs operation contracts and physical policy.
use super::*;
use Type::*;

pub(super) const CONTRACTS: &[Contract] = &[
    Contract::selectable(
        "pcs.commit",
        (
            &[ProverKey, Table],
            &[Commitment, OpeningState],
            AttributeRule::None,
        ),
    ),
    Contract::selectable(
        "pcs.open",
        (&[OpeningState, Point], &[Field, Proof], AttributeRule::None),
    ),
    Contract::selectable(
        "pcs.check",
        (
            &[VerifierKey, Commitment, Point, Field, Proof],
            &[Bool],
            AttributeRule::None,
        ),
    ),
    Contract::selectable(
        "pcs.equal",
        (&[Commitment, Commitment], &[Bool], AttributeRule::None),
    ),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    logical_refusals: &[],
    physical_error: "uninstalled operation binding",
    physical_only: false,

    contracts: CONTRACTS,
    resolve,
    providers: &["arkworks"],
    select: support::select_nominal,
};

fn resolve(
    binding: &OperationBinding,
    contract: &Contract,
) -> Result<KernelSignature<LogicalType>> {
    let shape = contract.shape()?;
    let primary = support::primary(binding)?;
    let field = primary.scalar_field().ok_or_else(support::failure)?;
    support::require_primary(binding, Identity::MultilinearKzgBls12381)?;
    support::instantiate(shape, field, |kind| match kind {
        Commitment | Proof | ProverKey | VerifierKey | OpeningState => {
            LogicalType::new(kind, primary)
        }
        _ => support::field_type(kind, field),
    })
}
