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
    let expected = if group {
        Identity::Bls12381G1
    } else {
        Identity::Bls12381Fr
    };
    support::require_primary(binding, expected)?;
    support::instantiate(contract.shape()?, Identity::Bls12381Fr, |kind| match kind {
        Group => LogicalType::new(kind, primary),
        _ => support::field_type(kind, Identity::Bls12381Fr),
    })
}
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled value encoding binding",
    physical_only: false,
    contracts: CONTRACTS,
    resolve,
    select: support::select_nominal,
};
