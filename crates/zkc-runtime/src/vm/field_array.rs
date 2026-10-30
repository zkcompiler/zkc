//! Logical fixed-length public field-array contracts. This layer selects no cryptographic code.

use super::operations::{Contribution, Installation};
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "binding-implementation",
    adapter: None,

    contracts: &[
        Installation::new("field_array.from_vector")
            .implemented_by(&["arkworks/field_array.from_vector"]),
        Installation::new("field_array.at").implemented_by(&["arkworks/field_array.at"]),
        Installation::new("field_array.get").implemented_by(&["arkworks/field_array.get"]),
    ],

    select: super::operations::default_ports,
};
