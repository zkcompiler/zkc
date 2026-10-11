//! Independently installed byte-data operations.
use super::*;
use Type::*;
pub(super) const CONTRACTS: &[Contract] = &[
    Contract::new("bytes.empty", (&[], &[Bytes], AttributeRule::None))
        .implemented_by(&["native/bytes.empty"]),
    Contract::new(
        "bytes.append",
        (&[Bytes, Index], &[Bytes], AttributeRule::None),
    )
    .implemented_by(&["native/bytes.append"]),
    Contract::new(
        "bytes.concat",
        (&[Bytes, Bytes], &[Bytes], AttributeRule::None),
    )
    .implemented_by(&["native/bytes.concat"]),
    Contract::new(
        "bytes.slice",
        (&[Bytes, Index, Index], &[Bytes], AttributeRule::None),
    )
    .implemented_by(&["native/bytes.slice"]),
    Contract::new("bytes.at", (&[Bytes, Index], &[Index], AttributeRule::None))
        .implemented_by(&["native/bytes.at"]),
    Contract::new("bytes.length", (&[Bytes], &[Index], AttributeRule::None))
        .implemented_by(&["native/bytes.length"]),
    Contract::new(
        "bytes.equal",
        (&[Bytes, Bytes], &[Bool], AttributeRule::None),
    )
    .implemented_by(&["native/bytes.equal"]),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled byte operation binding",
    physical_only: false,
    contracts: CONTRACTS,
    resolve: index::resolve,
    select: default_ports,
};
