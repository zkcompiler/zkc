//! Strict, independently resumable execution for explicitly bound participants.
//!
//! See `README.md` in this directory for admission, backend and transport contracts.
//! This module implements no cryptography. An installed backend owns value codecs,
//! capability issuance and state, shape admission, and mathematical operations.

mod admit;
mod backend;
mod bindings;
mod field_array;
mod fixed_vector;
mod operations;
mod resource_unit;
mod sequence;
mod services;
mod structural;
pub use services::{ServiceContract, ServicePort, ServiceSignature};
mod variant;
pub use resource_unit::ResourceDomain;
pub use structural::{
    ArgumentKind, NATURAL_ARGUMENT_LIMIT, STRUCTURAL_SPELLING_LIMIT, StructuralType,
    TYPE_DEPTH_LIMIT, TYPE_NODE_LIMIT, TypeArgument,
};
pub use variant::{VariantAlternative, VariantDescriptor};
mod decode;
mod model;
mod native_proof;
mod program;
pub use native_proof::{NativeProofEntry, NativeProofError, NativeTranscriptEvent};
pub use program::{ProgramAction, ProgramCut, ProgramRole, ProgramState};
mod runner;
mod transport;

pub use admit::{Admitted, EntryRole, admit_supplied};
pub use backend::{
    Backend, BackendError, Frame, FrameExit, FrameId, FrameKind, Invocation, ServiceInvocation,
    Value,
};
pub use bindings::{
    BoundSignature, Identity, LogicalType, OperationBinding, PhysicalType, Representation,
    ResolvedBinding,
};
pub use model::{
    AdmissionError, AttributeRule, ErrorCode, KernelSignature, Limits, LogicalOrigin, Type,
};
pub use runner::Runner;
pub use transport::{
    Action, Cut, CutKind, DecodeReason, Envelope, LoadError, LocalAction, LocalContext, Origin,
    Packet, PathElement, QueryAction, Receive, ReceiveCompletion, RuntimeError, Stop, StopKind,
    Usage, ValueBudget, WorkBudget,
};

#[cfg(test)]
mod control_tests;
#[cfg(test)]
mod tests;

mod domain_bindings;
