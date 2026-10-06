//! Separate-process artifact entry execution after source-relative admission.
//!
//! [`run`] enforces construction, participant and public-artifact profile
//! admission. The generic [`produce`] and [`validate`] driver primitives assume
//! a caller-admitted runner and root; using them directly does not establish
//! that profile. Remaining P sends and V receives are proof I/O. Transcript
//! effects stay in explicit local operations; no driver simulates a peer.

pub mod attempt;
mod driver;
mod entropy;
pub mod native;
mod wire;

pub use driver::{
    ArtifactFailure, ArtifactReport, Produced, produce, validate, validate_with_decoder,
};
pub use wire::{FormatError, MAX_PROOF_BYTES, ProofReader, ProofWriter};

mod configuration;
mod construction;
mod host;
mod identity;
mod inputs;
use crate::host::{inputs as io, json, material};
mod requirements;
pub use requirements::{ClaimRequirements, PhysicalChoices};
mod static_requirements;
pub use static_requirements::replay_static_requirements;
mod observe;
mod prepared;
pub use crate::host::admission::LoadLimits as InputLimits;
pub use construction::CheckedBundle;
pub use host::run;
pub use identity::inspect as inspect_identity;
pub use io::hex;
pub use material::{CacheLimits, CacheUsage};
pub use observe::{Observed, TraceMode};
pub use prepared::{
    ArtifactPaths, CheckerInstallation, InvocationError, InvocationInputs, InvocationOptions,
    PreparedArtifact, PreparedReport,
};

pub mod primitive;
