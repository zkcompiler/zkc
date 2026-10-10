//! Authenticated Entry packages, native run bundles and independent proof hosts.
pub mod entry;
mod host;
pub mod project;
pub mod proof;
pub mod run;
pub mod source_names;

/// Command discovery and file transport. Applications use entry, proof, or run.
pub mod cli;

/// Shared operational capacity, immutable input values and prover material.
pub mod execution {
    pub use crate::host::capacity::Capacity;
    pub use crate::host::input_file::InputFile;
    pub use crate::host::material::ProverMaterial;
    pub use crate::host::request::InputValue;
}
