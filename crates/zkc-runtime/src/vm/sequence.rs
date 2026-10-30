//! Logical sequence contracts, independent of physical storage and codecs.
use super::operations::{Contribution, Installation};

pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "binding-implementation",
    contracts: &[
        Installation::new("sequence.empty").implemented_by(&["native/sequence.empty"]),
        Installation::new("sequence.append").implemented_by(&["native/sequence.append"]),
        Installation::new("sequence.length").implemented_by(&["native/sequence.length"]),
        Installation::new("sequence.at").implemented_by(&["native/sequence.at"]),
    ],

    select: super::operations::default_ports,
};
