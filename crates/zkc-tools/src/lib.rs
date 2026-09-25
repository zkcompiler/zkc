//! Consumer-installed checker integration. The runtime never launches tools.
pub mod artifact;
mod checker;
pub mod groth16;
pub mod ingress;
pub mod noninteractive;
pub mod protocol;
pub mod snarkjs;
pub use checker::LeanChecker;
mod host;
pub mod table;
