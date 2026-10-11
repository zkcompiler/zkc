//! Resources backend contracts.
mod common;
#[path = "common/fixture.rs"]
mod fixture;
mod support;

#[path = "resources/opening_state.rs"]
mod opening_state;
#[path = "resources/parameter_limits.rs"]
mod parameter_limits;
#[path = "resources/resource_unit.rs"]
mod resource_unit;
#[path = "resources/resources.rs"]
mod resources;
#[path = "resources/retained_storage.rs"]
mod retained_storage;
#[path = "resources/setups.rs"]
mod setups;
