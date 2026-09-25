//! Strict, independently resumable execution for explicitly bound participants.
//!
//! See `README.md` in this directory for admission, backend and transport contracts.
//! This module implements no cryptography. An installed backend owns value codecs,
//! capability issuance and state, shape admission, and mathematical operations.

mod admit;
mod backend;
mod bindings;
mod resource_unit;
mod variant;
pub use resource_unit::ResourceDomain;
pub use variant::{VariantAlternative, VariantDescriptor};
mod decode;
mod driver;
mod model;
mod noninteractive;
mod runner;
mod source;
mod transport;

pub use admit::{Admitted, Correspondence, EntryRole, ReceivePort, admit_physical, admit_supplied};
pub use backend::{Backend, BackendError, Frame, FrameExit, FrameId, FrameKind, Invocation, Value};
pub use bindings::{
    ArtifactFormat, BoundSignature, Identity, LogicalType, OperationBinding, PhysicalType,
    Representation, ResolvedBinding,
};
pub use driver::{DriverCut, DriverEvent, drive_cut};
pub use model::{
    AdmissionError, AttributeRule, ErrorCode, KernelSignature, Limits, LogicalOrigin, Type,
};
pub use noninteractive::{NoninteractiveEntry, NoninteractiveError};
pub use runner::Runner;
pub use source::{CallMapping, PortMapping, SourceMap};
pub use transport::{
    Action, Cut, CutKind, Envelope, LoadError, LocalAction, Origin, Packet, PathElement, Receive,
    RuntimeError, Stop, StopKind, Usage, ValueBudget,
};

#[cfg(test)]
mod tests;

mod domain_bindings;

#[cfg(test)]
mod family_tests;
