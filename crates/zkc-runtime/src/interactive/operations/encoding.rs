//! Explicit external value encodings. Decode success is an ordinary Boolean.
use super::*;
use Type::*;
pub(super) const CONTRACTS: &[Contract] = &[
    Contract::new(
        "encoding.field_le",
        (&[Field], &[Bytes], AttributeRule::None),
    )
    .implemented_by(&["dalek/encoding.field_le"]),
    Contract::new(
        "encoding.field_from_le",
        (&[Bytes], &[Bool, Field], AttributeRule::None),
    )
    .implemented_by(&["dalek/encoding.field_from_le"]),
    Contract::new(
        "encoding.field_reduce_le",
        (&[Bytes], &[Field], AttributeRule::None),
    )
    .implemented_by(&["dalek/encoding.field_reduce_le"]),
    Contract::new(
        "encoding.group_decode_cofactor",
        (&[Bytes], &[Bool, Group], AttributeRule::None),
    )
    .implemented_by(&["dalek/encoding.group_decode_cofactor"]),
    Contract::new(
        "encoding.cryptonote_map",
        (&[Bytes], &[Group], AttributeRule::None),
    )
    .implemented_by(&["dalek/encoding.cryptonote_map"]),
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
    .implemented_by(&[
        "arkworks/encoding.group_compressed",
        "dalek/encoding.group_compressed",
    ]),
    Contract::new(
        "encoding.group_from_compressed",
        (&[Bytes], &[Bool, Group], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/encoding.group_from_compressed",
        "dalek/encoding.group_from_compressed",
    ]),
];
fn resolve(
    binding: &OperationBinding,
    contract: &Contract,
) -> Result<KernelSignature<LogicalType>> {
    let primary = support::primary(binding)?;
    let group = matches!(
        binding.contract.as_str(),
        "encoding.group_compressed"
            | "encoding.group_from_compressed"
            | "encoding.group_decode_cofactor"
            | "encoding.cryptonote_map"
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
    let primary = support::primary(binding)?;
    let allowed = match binding.contract.as_str() {
        "encoding.field_le" | "encoding.field_from_le" | "encoding.field_reduce_le" => {
            primary == Identity::Ristretto255Scalar
        }
        "encoding.group_decode_cofactor" | "encoding.cryptonote_map" => {
            primary == Identity::Edwards25519Prime
        }
        "encoding.group_compressed" | "encoding.group_from_compressed" => {
            matches!(primary, Identity::Bls12381G1 | Identity::Edwards25519Prime)
        }
        _ => primary == Identity::Bls12381Fr,
    };
    if !allowed {
        return Err(support::failure());
    }
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
