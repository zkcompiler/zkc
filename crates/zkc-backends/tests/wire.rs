//! Wire backend contracts.
mod common;
#[path = "common/fixture.rs"]
mod fixture;
mod support;

#[path = "wire/native_wire.rs"]
mod native_wire;
#[path = "wire/spongefish.rs"]
mod spongefish;
#[path = "wire/structured_wire.rs"]
mod structured_wire;
#[path = "wire/transcript.rs"]
mod transcript;
#[path = "wire/transport.rs"]
mod transport;
#[path = "wire/variants.rs"]
mod variants;
