//! Stable ownership of failures before an invocation produces an execution report.
use std::fmt;

/// The boundary that rejected an input, not the category of the defect.
/// Consult `EntryError::code` for the underlying reason.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EntryPhase {
    Package,
    Interface,
    Authority,
    Admission,
    Binding,
    /// The source adapter could not assemble the named request.
    Request,
    /// The native Host refused the assembled invocation, including invalid
    /// values, context or budgets that it checks independently.
    Preparation,
}
/// A preparation failure with its owning boundary. Execution and cleanup
/// failures remain in RunReport or ProofReport, including their resource usage.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EntryError {
    pub phase: EntryPhase,
    code: String,
}
impl EntryError {
    pub(crate) fn new(phase: EntryPhase, code: impl ToString) -> Self {
        Self {
            phase,
            code: code.to_string(),
        }
    }
    pub fn code(&self) -> &str {
        &self.code
    }
}
impl fmt::Display for EntryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.code)
    }
}
impl std::error::Error for EntryError {}
impl From<EntryError> for String {
    fn from(error: EntryError) -> Self {
        error.code
    }
}
pub(super) type EntryResult<T> = Result<T, EntryError>;

impl From<super::PackageError> for EntryError {
    fn from(error: super::PackageError) -> Self {
        Self::new(EntryPhase::Package, error)
    }
}
