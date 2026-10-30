//! Independently installed byte-data operations.
use super::*;
pub(super) const CONTRACTS: &[Installation] = &[
    Installation::new("bytes.repeat").implemented_by(&["native/bytes.repeat"]),
    Installation::new("bytes.join").implemented_by(&["native/bytes.join"]),
    Installation::new("bytes.empty").implemented_by(&["native/bytes.empty"]),
    Installation::new("bytes.append").implemented_by(&["native/bytes.append"]),
    Installation::new("bytes.concat").implemented_by(&["native/bytes.concat"]),
    Installation::new("bytes.slice").implemented_by(&["native/bytes.slice"]),
    Installation::new("bytes.at").implemented_by(&["native/bytes.at"]),
    Installation::new("bytes.length").implemented_by(&["native/bytes.length"]),
    Installation::new("bytes.equal").implemented_by(&["native/bytes.equal"]),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled byte operation binding",
    contracts: CONTRACTS,

    select: default_ports,
};
