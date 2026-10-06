//! Independently authored external operation contracts and physical policy.
use super::*;
use Type::*;

pub(super) const CONTRACTS: &[Contract] = &[
    Contract::new(
        "external.monero.init",
        (&[Indices], &[Indices], AttributeRule::None),
    ),
    Contract::new(
        "external.monero.hash",
        (&[Indices], &[Indices], AttributeRule::None),
    ),
    Contract::new(
        "external.monero.update",
        (
            &[Indices, Indices],
            &[Indices, Indices],
            AttributeRule::None,
        ),
    )
    .history(),
    Contract::new(
        "external.openvm.init",
        (&[], &[Indices], AttributeRule::None),
    ),
    Contract::new(
        "external.openvm.observe",
        (&[Indices, Indices], &[Indices], AttributeRule::None),
    )
    .history(),
    Contract::new(
        "external.openvm.sample",
        (&[Indices], &[Indices, Index], AttributeRule::None),
    )
    .history(),
    Contract::new(
        "external.openvm.sample_ext",
        (&[Indices], &[Indices, Indices], AttributeRule::None),
    )
    .history(),
    Contract::new(
        "external.openvm.sample_bits",
        (&[Indices, Index], &[Indices, Index], AttributeRule::None),
    )
    .history(),
    Contract::new(
        "external.openvm.check_witness",
        (
            &[Indices, Index, Index],
            &[Indices, Bool],
            AttributeRule::None,
        ),
    )
    .history(),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    logical_refusals: &[],
    physical_error: "uninstalled operation binding",
    physical_only: false,

    contracts: CONTRACTS,
    resolve: index::resolve,
    providers: &["native"],
    select: default_ports,
};
