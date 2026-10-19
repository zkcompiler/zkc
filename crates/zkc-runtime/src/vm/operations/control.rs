//! Independently authored control operation contracts and physical policy.
use super::*;
use Type::*;

pub(super) const CONTRACTS: &[Contract] = &[
    Contract::new("bool.and", (&[Bool, Bool], &[Bool], AttributeRule::None))
        .implemented_by(&["arkworks/bool.and"]),
    Contract::new("bool.or", (&[Bool, Bool], &[Bool], AttributeRule::None))
        .implemented_by(&["arkworks/bool.or"]),
    Contract::new("bool.not", (&[Bool], &[Bool], AttributeRule::None))
        .implemented_by(&["arkworks/bool.not"]),
    Contract::new("control.require", (&[Bool], &[], AttributeRule::None))
        .implemented_by(&["arkworks/control.require"]),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled operation binding",
    physical_only: false,

    contracts: CONTRACTS,
    resolve: index::resolve,
    select: default_ports,
};
