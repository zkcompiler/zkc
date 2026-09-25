//! Owned execution of checked logical plans. Libraries provide meanings;
//! the dispatcher owns binding and structured stopped control.
mod admission;
pub mod arena;
pub mod attempt;
pub mod buffer;
mod execution;
pub mod format;
pub mod iteration;
mod plan;
pub mod table;
pub use admission::{
    CheckFailure, CheckRequest, Checker, EndpointEntry, PhaseEvidence, Realization,
};
pub use execution::{
    AdmissionFailure, AdmittedJob, AdmittedProgram, BindingFailure, Bindings, Budget, Completed,
    Resources, Session, StartFailure,
};
pub use plan::{Library, Sort};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Error(pub &'static str);
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.0)
    }
}
impl std::error::Error for Error {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stop {
    Reject,
    Abort,
    Exhausted,
    Incomplete,
    Refused,
}
impl Stop {
    pub fn name(self) -> &'static str {
        match self {
            Self::Reject => "reject",
            Self::Abort => "abort",
            Self::Exhausted => "exhausted",
            Self::Incomplete => "incomplete",
            Self::Refused => "refused",
        }
    }
    pub fn decode(s: &str) -> Result<Self, Error> {
        match s {
            "reject" => Ok(Self::Reject),
            "abort" => Ok(Self::Abort),
            "exhausted" => Ok(Self::Exhausted),
            "incomplete" => Ok(Self::Incomplete),
            "refused" => Ok(Self::Refused),
            _ => Err(Error("unknown-stop")),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome<V> {
    Returned(V),
    Stopped(Stop),
}

/// Admitted, independently resumable interactive participant execution.
pub mod interactive;

/// Canonical construction trees and session-independent logical occurrences.
pub mod logical;
