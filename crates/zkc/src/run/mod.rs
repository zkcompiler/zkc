//! Native application authority and lifecycle for authenticated joint bundles.
mod host;
/// Installed units, scopes, defaults and maxima of the Host policy allowances.
pub use crate::host::capacity::{Allowance, Allowances, Scope};
pub use host::{
    EncodedOutput, HostLimits, HostReport, PreparedRun, RoleInputs, RoleOutputEncoding, RunHost,
    RunInputs, SetupAuthority,
};
