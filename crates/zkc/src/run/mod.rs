//! Native application authority and lifecycle for authenticated joint bundles.
mod host;
pub use host::{
    EncodedOutput, HostLimits, HostReport, PreparedRun, RoleInputs, RoleOutputEncoding, RunHost,
    RunInputs, SetupAuthority,
};
