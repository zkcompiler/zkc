//! Source Entry packages and their application-owned authentication boundary.
//!
//! Capturing a package authenticates its exact publication bytes. Execution must
//! additionally admit the native program and bind its interface; retained MLIR
//! is a compiler-checked subject, not an interpreter input for this host.
mod package;
pub use package::{CompileOptions, Package, PackageError};
