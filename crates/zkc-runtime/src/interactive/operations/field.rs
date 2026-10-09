//! Independently authored field operation contracts and physical policy.
use super::*;
use Type::*;

pub(super) const CONTRACTS: &[Contract] =
    &[
        Contract::selectable(
            "field.from_index",
            (&[Index], &[Field], AttributeRule::None),
        )
        .implemented_by(&[
            "arkworks/field.from_index",
            "dalek/field.from_index",
            "plonky3/field.from_index",
        ]),
        Contract::selectable(
            "field.sub",
            (&[Field, Field], &[Field], AttributeRule::None),
        )
        .implemented_by(&["arkworks/field.sub", "dalek/field.sub", "plonky3/field.sub"]),
        Contract::selectable("field.neg", (&[Field], &[Field], AttributeRule::None))
            .implemented_by(&["arkworks/field.neg", "dalek/field.neg", "plonky3/field.neg"]),
        Contract::selectable("field.inverse", (&[Field], &[Field], AttributeRule::None))
            .implemented_by(&[
                "arkworks/field.inverse",
                "dalek/field.inverse",
                "plonky3/field.inverse",
            ]),
        Contract::new("field.embed", (&[Field], &[Field], AttributeRule::None))
            .implemented_by(&["plonky3/field.embed"]),
        Contract::selectable(
            "field.constant",
            (&[], &[Field], AttributeRule::FieldDecimal),
        )
        .implemented_by(&[
            "arkworks/field.constant",
            "dalek/field.constant",
            "plonky3/field.constant",
        ]),
        Contract::selectable(
            "field.add",
            (&[Field, Field], &[Field], AttributeRule::None),
        )
        .implemented_by(&["arkworks/field.add", "dalek/field.add", "plonky3/field.add"]),
        Contract::selectable(
            "field.mul",
            (&[Field, Field], &[Field], AttributeRule::None),
        )
        .implemented_by(&["arkworks/field.mul", "dalek/field.mul", "plonky3/field.mul"]),
        Contract::selectable(
            "field.equal",
            (&[Field, Field], &[Bool], AttributeRule::None),
        )
        .implemented_by(&[
            "arkworks/field.equal",
            "dalek/field.equal",
            "plonky3/field.equal",
        ]),
    ];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled operation binding",
    physical_only: false,

    contracts: CONTRACTS,
    resolve,
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
