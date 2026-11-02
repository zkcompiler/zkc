//! Source Entry packages and their application-owned authentication boundary.
//!
//! Capturing a package authenticates its exact publication bytes. Execution must
//! additionally admit the native program, bind its interface and admit the
//! packaged expression assets its program references; retained MLIR is a
//! compiler-checked subject, not an interpreter input for this host.
pub mod oracle_selection;
pub use oracle_selection::{
    OracleAuthentication, OracleLeafGrouping, OracleLeafOrder, OracleQueryOrder,
    OracleRootSelection, OracleRoots, OracleSelection, OracleSelectionError,
    OracleTableRealization,
};
mod decode;
mod package;
#[cfg(feature = "cpu")]
pub(crate) use package::AuthenticatedArtifact;
pub use package::{CompileOptions, Package, PackageError, PackagedAsset};

mod errors;
pub use errors::{EntryCondition, EntryError, EntryPhase};
mod interface;
pub use interface::{
    BoundInterface, BoundaryRequirement, ComponentFacet, Interface, InterfaceError,
    InterfaceLimits, OrdinaryInput, PortComponent, ProtocolPort, PublicInputSelection,
    SelectionPurpose, ValuePlacement,
};
#[cfg(feature = "cpu")]
mod assets;
#[cfg(feature = "cpu")]
pub use assets::EntryAssets;

#[cfg(feature = "cpu")]
mod value;
#[cfg(feature = "cpu")]
pub use value::{OpaqueValue, Value};
mod function;
#[cfg(feature = "cpu")]
pub use function::cpu::{
    CallReceipt, FunctionEntry, FunctionFailure, FunctionOptions, FunctionReport, FunctionRequest,
    FunctionUsage, InvocationBinding, InvocationContext, PreparedFunction, ProofContext,
    RunContext, TypedValue,
};
pub use function::{
    Alternative, DeploymentInterface, Field, FunctionInterface, FunctionParameter,
    FunctionSignature, Permission, Schema, SchemaKind,
};
#[cfg(feature = "cpu")]
mod run;
#[cfg(feature = "cpu")]
pub use run::{
    EncodedRunResults, InputBoundRunEntry, NamedValues, PreparedRun, RoleInputs, RoleValues,
    RunEntry, RunReport, RunRequest,
};

/// Operational allowance for an omitted service or selected transcript budget.
/// Explicit budgets, including zero, override it; native hard limits still apply.
#[cfg(feature = "cpu")]
pub const DEFAULT_DRAW_BUDGET: u64 = crate::host::capacity::Allowances::SERVICE_DRAWS.default;
/// The installed maximum of any one service or selected transcript budget.
#[cfg(feature = "cpu")]
pub const MAX_DRAW_BUDGET: u64 = crate::host::capacity::Allowances::SERVICE_DRAWS.maximum;
#[cfg(feature = "cpu")]
mod arguments;
#[cfg(feature = "cpu")]
mod setups;
#[cfg(feature = "cpu")]
pub use setups::SetupAuthority;
#[cfg(feature = "cpu")]
mod proof;
#[cfg(feature = "cpu")]
pub use proof::{
    AttemptOptions, BindingPolicy, BindingScope, EncodedResults, OwnedEncodedResults, ProofCall,
    ProofEntry, ProofOperation, ProofOptions, ProofReport, ProofRequest, ProofResult,
    ResultRetention,
};

#[cfg(all(feature = "files", feature = "cpu"))]
pub mod files;
pub mod inputs;
#[cfg(feature = "cpu")]
pub mod memory;
#[cfg(feature = "cpu")]
pub mod outputs;

#[cfg(feature = "cpu")]
pub mod bindings;
#[cfg(all(feature = "cpu", any(test, feature = "test-utils")))]
pub mod testing;

#[cfg(feature = "cpu")]
mod backend;
#[cfg(feature = "cpu")]
pub use backend::{
    BackendRun, BindingError, ContextProducer, InputBindings, InputBoundBackendRun, InputComponent,
    InputRequirement, Observation,
};
