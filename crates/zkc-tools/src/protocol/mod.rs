//! Source-relative admission and explicit joint driving of independent roles.
//! A joint driver is a host policy; individual runners do not wait for peer cuts.
mod checker;
mod codecs;
mod driver;
mod host;
mod schedule;

pub use checker::ParticipantChecker;
pub use driver::{
    BackendDecoder, JointOutcome, JointReport, LocalTransport, MessageDecoder, Transport,
    WireBackend, WireUsage, drive, drive_with_decoder,
};
pub use host::run;
pub use schedule::{Schedule, ScheduledAction};
