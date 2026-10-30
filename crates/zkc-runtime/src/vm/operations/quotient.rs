//! Installed quotient-ring operation contracts.
use super::*;

const CONTRACTS: &[Installation] = &[
    Installation::new("quotient.prepare_matrix")
        .implemented_by(&["native/quotient.prepare_matrix"]),
    Installation::new("quotient.matvec").implemented_by(&["native/quotient.matvec"]),
    Installation::new("quotient.project").implemented_by(&["native/quotient.project"]),
    Installation::new("quotient.ntt").implemented_by(&["native/quotient.ntt"]),
    Installation::new("quotient.intt").implemented_by(&["native/quotient.intt"]),
    Installation::new("quotient.pointwise").implemented_by(&["native/quotient.pointwise"]),
    Installation::new("quotient.add").implemented_by(&["native/quotient.add"]),
    Installation::new("quotient.subtract").implemented_by(&["native/quotient.subtract"]),
    Installation::new("quotient.multiply").implemented_by(&["native/quotient.multiply"]),
    Installation::new("quotient.norm_within").implemented_by(&["native/quotient.norm_within"]),
];

pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled operation binding",
    contracts: CONTRACTS,

    select: default_ports,
};
