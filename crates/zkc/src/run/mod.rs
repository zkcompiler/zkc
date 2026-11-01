//! Native application authority and lifecycle for authenticated joint bundles.
mod host;
/// Installed defaults and maxima of the Host work allowances in [`HostLimits`].
pub use crate::host::capacity::{Allowance, Allowances};
pub use host::{
    EncodedOutput, HostLimits, HostReport, PreparedRun, RoleInputs, RoleOutputEncoding, RunHost,
    RunInputs, SetupAuthority,
};
