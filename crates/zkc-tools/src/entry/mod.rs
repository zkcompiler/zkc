//! Source Entry packages and their application-owned authentication boundary.
//!
//! Capturing a package authenticates its exact publication bytes. Execution must
//! additionally admit the native program and bind its interface; retained MLIR
//! is a compiler-checked subject, not an interpreter input for this host.
mod decode;
mod package;
pub use package::{CompileOptions, Package, PackageError};

mod interface;
pub use interface::{Interface, InterfaceError};

mod value;
pub use value::Value;
mod run;
pub use run::{NamedValues, PreparedRun, RoleInputs, RoleValues, RunEntry, RunReport, RunRequest};
