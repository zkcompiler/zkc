//! Explicit external value encodings. Decode success is an ordinary Boolean.
use super::*;
use Type::*;
pub(super) const CONTRACTS: &[Contract] = &[
    Contract::new(
        "encoding.field_be",
        (&[Field], &[Bytes], AttributeRule::None),
    )
    .implemented_by(&["arkworks/encoding.field_be"]),
    Contract::new(
        "encoding.field_from_be",
        (&[Bytes], &[Bool, Field], AttributeRule::None),
    )
    .implemented_by(&["arkworks/encoding.field_from_be"]),
    Contract::new(
        "encoding.field_reduce_be",
        (&[Bytes], &[Field], AttributeRule::None),
    )
    .implemented_by(&["arkworks/encoding.field_reduce_be"]),
    Contract::new(
        "encoding.group_compressed",
        (&[Group], &[Bytes], AttributeRule::None),
    )
    .implemented_by(&["arkworks/encoding.group_compressed"]),
    Contract::new(
        "encoding.group_from_compressed",
        (&[Bytes], &[Bool, Group], AttributeRule::None),
    )
    .implemented_by(&["arkworks/encoding.group_from_compressed"]),
];
fn resolve(
    binding: &OperationBinding,
    contract: &Contract,
) -> Result<KernelSignature<LogicalType>> {
    let primary = support::primary(binding)?;
    let group = matches!(
        binding.contract.as_str(),
        "encoding.group_compressed" | "encoding.group_from_compressed"
    );
    let field = primary.scalar_field().ok_or_else(support::failure)?;
    if binding.arguments.len() != 1
        || if group {
            primary.group() != Some(primary)
        } else {
            field != primary
        }
    {
        return Err(support::failure());
    }
    support::instantiate(contract.shape()?, field, |kind| match kind {
        Group => LogicalType::new(kind, primary),
        _ => support::field_type(kind, field),
    })
}
fn select(
    binding: &OperationBinding,
    logical: &KernelSignature<LogicalType>,
    selection: Selection,
) -> Result<BoundSignature> {
    // Logical formation is generic. The installed byte algorithms are the
    // BLS12-381 scalar and compressed G1 encodings, selected independently.
    let group = matches!(
        binding.contract.as_str(),
        "encoding.group_compressed" | "encoding.group_from_compressed"
    );
    support::require_primary(
        binding,
        if group {
            Identity::Bls12381G1
        } else {
            Identity::Bls12381Fr
        },
    )?;
    support::select_nominal(binding, logical, selection)
}
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled value encoding binding",
    physical_only: false,
    contracts: CONTRACTS,
    resolve,
    select,
};
