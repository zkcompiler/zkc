//! Independently authored external operation contracts and physical policy.
use super::*;
use Type::*;

pub(super) const CONTRACTS: &[Contract] = &[
    Contract::new(
        "external.monero.init",
        (&[Indices], &[Indices], AttributeRule::None),
    )
    .implemented_by(&["native/external.monero.init"]),
    Contract::new(
        "external.monero.hash",
        (&[Indices], &[Indices], AttributeRule::None),
    )
    .implemented_by(&["native/external.monero.hash"]),
    Contract::new(
        "external.monero.update",
        (
            &[Indices, Indices],
            &[Indices, Indices],
            AttributeRule::None,
        ),
    )
    .implemented_by(&["native/external.monero.update"])
    .history(),
    Contract::new(
        "external.openvm.init",
        (&[], &[Indices], AttributeRule::None),
    )
    .implemented_by(&["native/external.openvm.init"]),
    Contract::new(
        "external.openvm.observe",
        (&[Indices, Indices], &[Indices], AttributeRule::None),
    )
    .implemented_by(&["native/external.openvm.observe"])
    .history(),
    Contract::new(
        "external.openvm.sample",
        (&[Indices], &[Indices, Index], AttributeRule::None),
    )
    .implemented_by(&["native/external.openvm.sample"])
    .history(),
    Contract::new(
        "external.openvm.sample_ext",
        (&[Indices], &[Indices, Indices], AttributeRule::None),
    )
    .implemented_by(&["native/external.openvm.sample_ext"])
    .history(),
    Contract::new(
        "external.openvm.sample_bits",
        (&[Indices, Index], &[Indices, Index], AttributeRule::None),
    )
    .implemented_by(&["native/external.openvm.sample_bits"])
    .history(),
    Contract::new(
        "external.openvm.check_witness",
        (
            &[Indices, Index, Index],
            &[Indices, Bool],
            AttributeRule::None,
        ),
    )
    .implemented_by(&["native/external.openvm.check_witness"])
    .history(),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled operation binding",
    physical_only: false,

    contracts: CONTRACTS,
    resolve: index::resolve,
    select: default_ports,
};
