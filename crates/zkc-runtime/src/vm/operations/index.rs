//! Installed index operation implementations and physical policy.
use super::*;

pub(super) const CONTRACTS: &[Installation] = &[
    Installation::new("index.constant").implemented_by(&["native/index.constant"]),
    Installation::new("index.add").implemented_by(&["native/index.add"]),
    Installation::new("index.sub").implemented_by(&["native/index.sub"]),
    Installation::new("index.mul").implemented_by(&["native/index.mul"]),
    Installation::new("index.div").implemented_by(&["native/index.div"]),
    Installation::new("index.mod").implemented_by(&["native/index.mod"]),
    Installation::new("index.equal").implemented_by(&["native/index.equal"]),
    Installation::new("index.less").implemented_by(&["native/index.less"]),
    Installation::new("indices.empty").implemented_by(&["native/indices.empty"]),
    Installation::new("indices.append").implemented_by(&["native/indices.append"]),
    Installation::new("indices.at").implemented_by(&["native/indices.at"]),
    Installation::new("indices.length").implemented_by(&["native/indices.length"]),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled operation binding",
    adapter: None,

    contracts: CONTRACTS,

    select: default_ports,
};
