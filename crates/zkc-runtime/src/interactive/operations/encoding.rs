//! Explicit external value encodings. Decode success is an ordinary Boolean.
use super::*;
use Type::*;
pub(super) const CONTRACTS: &[Contract] = &[
    Contract::new(
        "encoding.index_uleb128",
        (&[Index], &[Bytes], AttributeRule::None),
    )
    .implemented_by(&["native/encoding.index_uleb128"]),
    Contract::new(
        "encoding.fields_be",
        (&[Vector], &[Bytes], AttributeRule::None),
    )
    .implemented_by(&["arkworks/encoding.fields_be"]),
    Contract::new(
        "encoding.fields_le",
        (&[Vector], &[Bytes], AttributeRule::None),
    )
    .implemented_by(&["dalek/encoding.fields_le"]),
    Contract::new(
        "encoding.groups_compressed",
        (&[Groups], &[Bytes], AttributeRule::None),
    )
    .implemented_by(&[
        "arkworks/encoding.groups_compressed",
        "dalek/encoding.groups_compressed",
    ]),
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
    if binding.contract == "encoding.index_uleb128" {
        return index::resolve(binding, contract);
    }
    let primary = support::primary(binding)?;
    let group = matches!(
        binding.contract.as_str(),
        "encoding.group_compressed"
            | "encoding.groups_compressed"
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
        Group | Groups => LogicalType::new(kind, primary),
        _ => support::field_type(kind, field),
    })
}
fn select(
    binding: &OperationBinding,
    logical: &KernelSignature<LogicalType>,
    selection: Selection,
) -> Result<BoundSignature> {
    if binding.contract == "encoding.index_uleb128" {
        return default_ports(binding, logical, selection);
    }
    let primary = support::primary(binding)?;
    let allowed = match binding.contract.as_str() {
        "encoding.field_le"
        | "encoding.fields_le"
        | "encoding.field_from_le"
        | "encoding.field_reduce_le" => primary == Identity::Ristretto255Scalar,
        "encoding.group_decode_cofactor" | "encoding.cryptonote_map" => {
            primary == Identity::Edwards25519Prime
        }
        "encoding.group_compressed"
        | "encoding.groups_compressed"
        | "encoding.group_from_compressed" => {
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
