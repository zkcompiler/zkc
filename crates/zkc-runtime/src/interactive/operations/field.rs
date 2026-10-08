//! Independently authored field operation contracts and physical policy.
use super::*;
use Type::*;

pub(super) const CONTRACTS: &[Contract] = &[
    Contract::selectable(
        "field.from_index",
        (&[Index], &[Field], AttributeRule::None),
    ),
    Contract::selectable(
        "field.sub",
        (&[Field, Field], &[Field], AttributeRule::None),
    ),
    Contract::selectable("field.neg", (&[Field], &[Field], AttributeRule::None)),
    Contract::selectable("field.inverse", (&[Field], &[Field], AttributeRule::None)),
    Contract::new("field.embed", (&[Field], &[Field], AttributeRule::None)),
    Contract::selectable(
        "field.constant",
        (&[], &[Field], AttributeRule::FieldDecimal),
    ),
    Contract::selectable(
        "field.add",
        (&[Field, Field], &[Field], AttributeRule::None),
    ),
    Contract::selectable(
        "field.mul",
        (&[Field, Field], &[Field], AttributeRule::None),
    ),
    Contract::selectable(
        "field.equal",
        (&[Field, Field], &[Bool], AttributeRule::None),
    ),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled operation binding",
    physical_only: false,

    contracts: CONTRACTS,
    resolve,
    providers: &["arkworks", "dalek", "plonky3"],
    select: support::select_nominal,
};

fn resolve(
    binding: &OperationBinding,
    contract: &Contract,
) -> Result<KernelSignature<LogicalType>> {
    let mut signature = support::field_signature(binding, contract)?;
    if binding.contract == "field.embed" {
        let base = support::primary(binding)?
            .base_field()
            .ok_or_else(support::failure)?;
        *signature.inputs.first_mut().ok_or_else(support::failure)? =
            LogicalType::new(Field, base)?;
    }
    Ok(signature)
}
