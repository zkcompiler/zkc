//! Supplied run bundles and deterministic joint execution of their roles.
//! Anchors describe the supplied schedule; they do not prove source correspondence.
mod bundle;
mod decode;
mod structure;
pub use bundle::{Bundle, BundleError, BundleLimits, Segment, Step};
mod report;
mod session;
use super::wire::{WireBackend, WireError};
pub use report::{
    Failure, FailureKind, Observation, Outcome, PendingMessage, Phase, Progress, Reached, Report,
    RoleReport, State, StopCause, StopSummary, Text, WireUsage,
};
pub use session::{
    Exchange, Hooks, NoHooks, RoleInput, RunLimits, StartError, run, run_with_ledger,
};
