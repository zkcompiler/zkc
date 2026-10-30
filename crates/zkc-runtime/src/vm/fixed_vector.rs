//! Logical field-vector contracts. This layer selects no cryptographic code.

use super::operations::{Contribution, Installation};
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "binding-implementation",

    contracts: &[
        Installation::new("fixed_vector.from_vector")
            .implemented_by(&["plonky3/fixed_vector.from_vector"]),
        Installation::new("fixed_vector.to_vector")
            .implemented_by(&["plonky3/fixed_vector.to_vector"]),
        Installation::new("fixed_vector.dot").implemented_by(&["plonky3/fixed_vector.dot"]),
    ],

    select: super::operations::default_ports,
};
