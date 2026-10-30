//! Installed oracle operation implementations and physical policy.
use super::*;

pub(super) const CONTRACTS: &[Installation] = &[
    Installation::new("oracle.commit").implemented_by(&["plonky3/oracle.commit"]),
    Installation::new("oracle.open").implemented_by(&["plonky3/oracle.open"]),
    Installation::new("oracle.check").implemented_by(&["plonky3/oracle.check"]),
    Installation::new("oracle.open_many").implemented_by(&["plonky3/oracle.open_many"]),
    Installation::new("oracle.check_many").implemented_by(&["plonky3/oracle.check_many"]),
    Installation::new("commitments.empty").implemented_by(&["plonky3/commitments.empty"]),
    Installation::new("commitments.append").implemented_by(&["plonky3/commitments.append"]),
    Installation::new("commitments.at").implemented_by(&["plonky3/commitments.at"]),
    Installation::new("commitments.length").implemented_by(&["plonky3/commitments.length"]),
    Installation::new("opening_states.empty").implemented_by(&["plonky3/opening_states.empty"]),
    Installation::new("opening_states.append").implemented_by(&["plonky3/opening_states.append"]),
    Installation::new("opening_states.at").implemented_by(&["plonky3/opening_states.at"]),
    Installation::new("opening_states.length").implemented_by(&["plonky3/opening_states.length"]),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled operation binding",

    contracts: CONTRACTS,

    select: default_ports,
};
