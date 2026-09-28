//! Independently authored random contracts and admission.
use super::*;
use Type::*;

pub(super) const CONTRACTS: &[Contract] = &[
    Contract::new(
        "random.vector",
        (&[Rng], &[Vector, Rng], AttributeRule::NaturalIndex),
    ),
    Contract::new(
        "random.index",
        (&[Rng, Index], &[Index, Rng], AttributeRule::None),
    ),
    Contract::new("random.draw", (&[Rng], &[Field, Rng], AttributeRule::None)),
    Contract::new(
        "random.draw_nonzero",
        (&[Rng], &[NonzeroField, Rng], AttributeRule::None),
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
    support::require_primary(binding, field)?;
    if binding.contract == "random.index" && primary != Identity::KoalaBearExt8 {
        return Err(support::failure());
    }
    support::instantiate(shape, field, |kind| support::field_type(kind, field))
}

fn select(
    binding: &OperationBinding,
    logical: &KernelSignature<LogicalType>,
    selection: Selection,
) -> Result<BoundSignature> {
    selection.require_default()?;
    support::select_nominal(binding, logical, selection)
}
