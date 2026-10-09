//! Authenticated Entry packages, native run bundles and independent proof hosts.
pub mod entry;
mod host;
pub mod proof;
pub mod run;

/// Command discovery and file transport. Applications use entry, proof, or run.
pub mod cli;
