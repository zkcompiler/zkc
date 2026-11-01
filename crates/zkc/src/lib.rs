//! Authenticated Entry packages, native run bundles and independent proof hosts.
pub mod entry;
#[cfg(feature = "evm")]
pub mod evm;
#[cfg(feature = "cpu")]
mod host;
mod io;
#[cfg(feature = "project")]
pub mod project;
#[cfg(feature = "cpu")]
pub mod proof;
#[cfg(feature = "cpu")]
pub mod run;
pub mod source_names;

/// Shared CPU execution, operational capacity, immutable inputs and prover material.
#[cfg(feature = "cpu")]
pub mod execution {
    pub use zkc_cpu::{CpuExecution, CpuInstallation, providers};

    pub use crate::host::capacity::Capacity;
    pub use crate::host::data::PreparedData;
    pub use crate::host::input_source::InputSource;
    pub use crate::host::material::ProverMaterial;
    pub use crate::host::request::InputValue;
}

/// Bounded file ingress and atomic artifact publication.
#[cfg(feature = "files")]
pub mod files;

/// Whether this build explicitly enabled execution instrumentation.
#[cfg(feature = "cpu")]
pub const EXECUTION_COUNTS_ENABLED: bool = zkc_runtime::vm::ExecutionCounts::ENABLED;
