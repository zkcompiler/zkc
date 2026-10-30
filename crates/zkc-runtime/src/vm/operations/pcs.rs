//! Installed pcs operation implementations and physical policy.
use super::*;

pub(super) const CONTRACTS: &[Installation] = &[
    Installation::selectable("pcs.commit").implemented_by(&["arkworks/pcs.commit"]),
    Installation::selectable("pcs.open").implemented_by(&["arkworks/pcs.open"]),
    Installation::selectable("pcs.check").implemented_by(&["arkworks/pcs.check"]),
    Installation::selectable("pcs.equal").implemented_by(&["arkworks/pcs.equal"]),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled operation binding",

    contracts: CONTRACTS,

    select: support::select_nominal,
};
