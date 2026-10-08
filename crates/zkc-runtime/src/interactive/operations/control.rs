//! Independently authored control operation contracts and physical policy.
use super::*;
use Type::*;

pub(super) const CONTRACTS: &[Contract] = &[
    Contract::new("bool.and", (&[Bool, Bool], &[Bool], AttributeRule::None)),
    Contract::new("bool.or", (&[Bool, Bool], &[Bool], AttributeRule::None)),
    Contract::new("bool.not", (&[Bool], &[Bool], AttributeRule::None)),
    Contract::new("control.require", (&[Bool], &[], AttributeRule::None)),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled operation binding",
    physical_only: false,

    contracts: CONTRACTS,
    resolve: index::resolve,
    providers: &["arkworks"],
    select: default_ports,
};
