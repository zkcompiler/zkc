//! Native application authority and lifecycle for authenticated joint bundles.
mod host;
pub use host::{
    HostLimits, HostReport, PreparedRun, RoleInputs, RunHost, RunInputs, SetupAuthority,
};
pub(crate) mod cli;
