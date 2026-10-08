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

/// Operational allowance for an omitted service or selected transcript budget.
/// Explicit budgets, including zero, override it; native hard limits still apply.
pub const DEFAULT_DRAW_BUDGET: u64 = crate::host::inputs::RESOURCE_BUDGET_LIMIT;
mod arguments;
mod setups;
pub use setups::SetupAuthority;
mod proof;
pub use proof::{
    AttemptOptions, BindingPolicy, BindingScope, ProofEntry, ProofOptions, ProofReport,
    ProofRequest,
};

pub mod files;

pub mod cli;

pub mod bindings;
