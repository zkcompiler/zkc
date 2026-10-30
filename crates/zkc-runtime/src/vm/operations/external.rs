//! Installed external operation implementations and physical policy.
use super::*;

pub(super) const CONTRACTS: &[Installation] = &[
    Installation::new("external.monero.init").implemented_by(&["native/external.monero.init"]),
    Installation::new("external.monero.hash").implemented_by(&["native/external.monero.hash"]),
    Installation::new("external.monero.update").implemented_by(&["native/external.monero.update"]),
    Installation::new("external.openvm.init").implemented_by(&["native/external.openvm.init"]),
    Installation::new("external.openvm.observe")
        .implemented_by(&["native/external.openvm.observe"]),
    Installation::new("external.openvm.sample").implemented_by(&["native/external.openvm.sample"]),
    Installation::new("external.openvm.sample_ext")
        .implemented_by(&["native/external.openvm.sample_ext"]),
    Installation::new("external.openvm.sample_bits")
        .implemented_by(&["native/external.openvm.sample_bits"]),
    Installation::new("external.openvm.check_witness")
        .implemented_by(&["native/external.openvm.check_witness"]),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled operation binding",

    contracts: CONTRACTS,

    select: default_ports,
};
