//! Installed control operation implementations and physical policy.
use super::*;

pub(super) const CONTRACTS: &[Installation] = &[
    Installation::new("bool.and").implemented_by(&["arkworks/bool.and"]),
    Installation::new("bool.or").implemented_by(&["arkworks/bool.or"]),
    Installation::new("bool.not").implemented_by(&["arkworks/bool.not"]),
    Installation::new("control.require").implemented_by(&["arkworks/control.require"]),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled operation binding",

    contracts: CONTRACTS,

    select: default_ports,
};
