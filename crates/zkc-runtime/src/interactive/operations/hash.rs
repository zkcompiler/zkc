//! Copyable hash snapshots; these operations do not own sampling authority.
use super::*;
use Type::*;
pub(super) const CONTRACTS: &[Contract] = &[
    Contract::new("hash.keccak256", (&[Bytes], &[Bytes], AttributeRule::None))
        .implemented_by(&["native/hash.keccak256"]),
    Contract::new(
        "shake128.init",
        (&[], &[Shake128State], AttributeRule::None),
    )
    .implemented_by(&["native/shake128.init"]),
    Contract::new(
        "shake128.absorb",
        (
            &[Shake128State, Bytes],
            &[Shake128State],
            AttributeRule::None,
        ),
    )
    .implemented_by(&["native/shake128.absorb"])
    .history(),
    Contract::new(
        "shake128.squeeze",
        (
            &[Shake128State, Index],
            &[Shake128State, Bytes],
            AttributeRule::None,
        ),
    )
    .implemented_by(&["native/shake128.squeeze"])
    .history(),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled hash operation binding",
    physical_only: false,
    contracts: CONTRACTS,
    resolve: index::resolve,
    select: default_ports,
};
