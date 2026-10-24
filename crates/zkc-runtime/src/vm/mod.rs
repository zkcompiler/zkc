//! Virtual-machine programs, execution contracts, and instance state.
//!
//! See `README.md` in this directory for admission, backend and transport contracts.
//! This module implements no cryptography. An installed backend owns value codecs,
//! capability issuance and state, shape admission, and mathematical operations.

mod admit;
mod aggregate_bindings;
pub use aggregate_bindings::AggregateImplementationFamily;
pub(crate) mod backend;
mod bindings;
mod contracts;
mod physical;
pub use contracts::{
    AggregateChildRule, AuthorizationId, Contracts, ContractsBuilder, ExecutionPolicy,
    ExtensionRepresentation, ImplementationId, ImplementationRequirements, TimingRequirement,
    WireCodec,
};
pub(crate) mod execution_ledger;
mod field_array;
mod fixed_vector;
mod link;
pub use execution_ledger::{
    ExecutionLedger, ExecutionLedgerUsage, LiveReservation, RetainedOutputs,
};
mod operations;
mod resource_unit;
mod sequence;
mod services;
mod structural;
pub use services::{ServiceContract, ServicePort, ServiceSignature, ServiceSupport};
mod variant;
pub use resource_unit::ResourceDomain;
pub use structural::{
    ArgumentKind, NATURAL_ARGUMENT_LIMIT, STRUCTURAL_SPELLING_LIMIT, StructuralType,
    TYPE_DEPTH_LIMIT, TYPE_NODE_LIMIT, TypeArgument,
};
pub use variant::{VariantAlternative, VariantDescriptor};
pub(crate) mod code;
mod decode;
mod model;
mod native_proof;
pub(crate) mod preparation;
mod program;
pub(crate) mod retention;
pub use native_proof::{
    ConstructionPlan, NativeProofEntry, NativeProofError, NativeProofOperation,
    NativeTranscriptEvent, ProofConstruction,
};
pub use preparation::{PreparationLimits, PreparationStats, PreparedComputations};
pub use program::{AssetReference, ProgramAction, ProgramCut, ProgramRole, ProgramState};
pub use retention::{Backing, Retained};
pub(crate) mod counts;
pub use counts::ExecutionCounts;
mod observe;

pub use admit::{EntryRole, LocalFunction, Program};
pub use backend::{
    Backend, BackendError, CallContext, Frame, FrameExit, FrameId, FrameInputs, FrameKind,
    InstalledOperation, Invocation, ServiceInvocation, Value,
};
pub use bindings::{
    BoundSignature, Identity, LogicalType, OperationBinding, PhysicalType, Representation,
    ResolvedBinding, bit_pattern_literal,
};
pub use model::{
    AdmissionError, AttributeRule, ErrorCode, Limits, LogicalOrigin, OperationSignature, Type,
};
pub use observe::{
    Action, Cut, CutKind, DecodeReason, Envelope, LoadError, LocalAction, LocalContext, Origin,
    Packet, PathElement, QueryAction, Receive, ReceiveCompletion, RuntimeError, Stop, StopKind,
    Usage, ValueBudget, WorkBudget,
};

#[cfg(test)]
mod control_tests;
#[cfg(test)]
mod tests;

mod domain_bindings;

#[cfg(test)]
use crate::interpreter::Runner;

pub(crate) mod instance;
