//! Generated declaration data, independent of MLIR, installation and execution.
//!
//! A catalog row describes a logical contract. It neither installs a backend nor
//! admits a source application, supplies a formal interpretation, or permits
//! moving a reached operation. Consumer profiles retain those responsibilities.

mod model;
pub use model::*;

include!(concat!(env!("OUT_DIR"), "/catalog.rs"));

/// Look up exact nominal identity; array position has no semantic authority.
pub fn operation(name: &str) -> Option<&'static Operation> {
    CATALOG.operations.iter().find(|row| row.name == name)
}

pub fn constructor(name: &str) -> Option<&'static TypeConstructor> {
    CATALOG.types.iter().find(|row| row.name == name)
}

pub fn consumer_profile(name: &str) -> Option<&'static ConsumerProfile> {
    CATALOG
        .consumer_profiles
        .iter()
        .find(|row| row.name == name)
}

/// Query a fixed owner-selected profile. Actual arguments, domain capabilities,
/// implementation selection and invocation parameters require separate checks.
pub fn consumer_profile_operation(
    profile: &str,
    operation: &str,
) -> Option<&'static ConsumerProfileOperation> {
    consumer_profile(profile)?
        .operations
        .iter()
        .find(|row| row.operation == operation)
}
