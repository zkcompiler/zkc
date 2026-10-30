//! Explicit external value encodings. Decode success is an ordinary Boolean.
use super::*;
pub(super) const CONTRACTS: &[Installation] = &[
    Installation::new("encoding.index_uleb128").implemented_by(&["native/encoding.index_uleb128"]),
    Installation::new("encoding.fields_be").implemented_by(&["arkworks/encoding.fields_be"]),
    Installation::new("encoding.fields_from_be")
        .implemented_by(&["arkworks/encoding.fields_from_be"]),
    Installation::new("encoding.fields_le")
        .implemented_by(&["dalek/encoding.fields_le", "plonky3/encoding.fields_le"]),
    Installation::new("encoding.groups_compressed").implemented_by(&[
        "arkworks/encoding.groups_compressed",
        "dalek/encoding.groups_compressed",
    ]),
    Installation::new("encoding.field_le")
        .implemented_by(&["dalek/encoding.field_le", "plonky3/encoding.field_le"]),
    Installation::new("encoding.field_from_le").implemented_by(&[
        "dalek/encoding.field_from_le",
        "plonky3/encoding.field_from_le",
    ]),
    Installation::new("encoding.fields_from_le")
        .implemented_by(&["plonky3/encoding.fields_from_le"]),
    Installation::new("encoding.field_montgomery_le")
        .implemented_by(&["plonky3/encoding.field_montgomery_le"]),
    Installation::new("encoding.field_from_montgomery_le")
        .implemented_by(&["plonky3/encoding.field_from_montgomery_le"]),
    Installation::new("encoding.fields_montgomery_le")
        .implemented_by(&["plonky3/encoding.fields_montgomery_le"]),
    Installation::new("encoding.fields_from_montgomery_le")
        .implemented_by(&["plonky3/encoding.fields_from_montgomery_le"]),
    Installation::new("encoding.field_reduce_le")
        .implemented_by(&["dalek/encoding.field_reduce_le"]),
    Installation::new("encoding.group_decode_cofactor")
        .implemented_by(&["dalek/encoding.group_decode_cofactor"]),
    Installation::new("encoding.cryptonote_map").implemented_by(&["dalek/encoding.cryptonote_map"]),
    Installation::new("encoding.field_be").implemented_by(&["arkworks/encoding.field_be"]),
    Installation::new("encoding.field_from_be")
        .implemented_by(&["arkworks/encoding.field_from_be"]),
    Installation::new("encoding.field_reduce_be")
        .implemented_by(&["arkworks/encoding.field_reduce_be"]),
    Installation::new("encoding.group_compressed").implemented_by(&[
        "arkworks/encoding.group_compressed",
        "dalek/encoding.group_compressed",
    ]),
    Installation::new("encoding.group_from_compressed").implemented_by(&[
        "arkworks/encoding.group_from_compressed",
        "dalek/encoding.group_from_compressed",
    ]),
];

fn select(
    binding: &OperationBinding,
    logical: &OperationSignature<LogicalType>,
    selection: Selection,
) -> Result<BoundSignature> {
    if binding.contract == "encoding.index_uleb128" {
        return default_ports(binding, logical, selection);
    }
    let primary = support::primary(binding)?;
    // Four-byte coordinate words cover KoalaBear and its installed extensions.
    let residue = primary.is_plonky3_residue();
    // Binary fields have little-endian bit patterns; Montgomery residues are
    // defined only for prime fields and their extensions.
    let binary = primary.bit_pattern_width().is_some();
    let allowed = match binding.contract.as_str() {
        "encoding.field_le" | "encoding.fields_le" | "encoding.field_from_le" => {
            primary == Identity::Ristretto255Scalar || residue || binary
        }
        "encoding.field_reduce_le" => primary == Identity::Ristretto255Scalar,
        "encoding.fields_from_le" => residue || binary,
        "encoding.field_montgomery_le"
        | "encoding.field_from_montgomery_le"
        | "encoding.fields_montgomery_le"
        | "encoding.fields_from_montgomery_le" => primary.has_montgomery_words(),
        "encoding.group_decode_cofactor" | "encoding.cryptonote_map" => {
            primary == Identity::Edwards25519Prime
        }
        "encoding.groups_compressed" => {
            matches!(primary, Identity::Bls12381G1 | Identity::Edwards25519Prime)
        }
        "encoding.group_compressed" | "encoding.group_from_compressed" => matches!(
            primary,
            Identity::Bls12381G1 | Identity::Bls12381G2 | Identity::Edwards25519Prime
        ),
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
    contracts: CONTRACTS,

    select,
};
