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
    /// A packaged expression asset was refused, or an admitted program names
    /// an asset the package does not carry in a compatible carrier field.
    Assets,
    /// The source adapter could not assemble the named request.
    Request,
    /// The native Host refused the assembled invocation, including invalid
    /// values, context or budgets that it checks independently.
    Preparation,
}
/// A refusal condition that run, proof and Function entries share. Each
/// condition has exactly one code and one phase in every Entry kind; a
/// condition that only one kind can meet keeps that kind's own code.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EntryCondition {
    /// The interface document is malformed.
    InterfaceFormat,
    /// The interface does not identify the package's original source.
    InterfaceIdentity,
    /// An input or parameter type has custody or cannot be copied.
    InputCustody,
    /// A request or context names a role the Entry does not have.
    InputRoles,
    /// Named inputs, arguments or context inputs do not cover their ports
    /// exactly: a name is unknown, missing or supplied twice.
    InputNames,
    /// A prover-key port receives a value that is not a prover key.
    InputKey,
    /// A service allowance names a service the role does not have.
    ServiceNames,
    /// A service or selected transcript draw allowance exceeds the installed
    /// maximum.
    ServiceBudget,
}
impl EntryCondition {
    pub const fn code(self) -> &'static str {
        match self {
            Self::InterfaceFormat => "entry-interface-format",
            Self::InterfaceIdentity => "entry-interface-identity",
            Self::InputCustody => "entry-input-custody",
            Self::InputRoles => "entry-input-roles",
            Self::InputNames => "entry-input-names",
            Self::InputKey => "entry-input-key",
            Self::ServiceNames => "entry-service-names",
            Self::ServiceBudget => "entry-service-budget",
        }
    }
    pub const fn phase(self) -> EntryPhase {
        match self {
            Self::InterfaceFormat | Self::InterfaceIdentity | Self::InputCustody => {
                EntryPhase::Interface
            }
            Self::InputRoles | Self::InputNames | Self::InputKey | Self::ServiceNames => {
                EntryPhase::Request
            }
            Self::ServiceBudget => EntryPhase::Preparation,
        }
    }
    /// The condition a code names, if it is a shared condition.
    pub fn from_code(code: &str) -> Option<Self> {
        [
            Self::InterfaceFormat,
            Self::InterfaceIdentity,
            Self::InputCustody,
            Self::InputRoles,
            Self::InputNames,
            Self::InputKey,
            Self::ServiceNames,
            Self::ServiceBudget,
        ]
        .into_iter()
        .find(|condition| condition.code() == code)
    }
}
impl From<EntryCondition> for EntryError {
    fn from(condition: EntryCondition) -> Self {
        Self::new(condition.phase(), condition.code())
    }
}
impl From<EntryCondition> for String {
    fn from(condition: EntryCondition) -> Self {
        condition.code().into()
    }
}
/// A preparation failure with its owning boundary. Execution and cleanup
/// failures remain in RunReport or ProofReport, including their resource usage.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EntryError {
    pub phase: EntryPhase,
    code: String,
    path: Option<String>,
}
impl EntryError {
    pub(crate) fn new(phase: EntryPhase, code: impl ToString) -> Self {
        Self {
            phase,
            code: code.to_string(),
            path: None,
        }
    }
    /// A refusal at `phase`, unless its code names a shared condition, whose
    /// own phase is the same in every Entry kind.
    pub(crate) fn at(phase: EntryPhase, code: impl ToString) -> Self {
        let code = code.to_string();
        match EntryCondition::from_code(&code) {
            Some(condition) => condition.into(),
            None => Self::new(phase, code),
        }
    }
    #[cfg(feature = "cpu")]
    pub(crate) fn boundary(
        phase: EntryPhase,
        code: impl ToString,
        interface: &super::Interface,
    ) -> Self {
        Self::boundary_for_role(phase, code, interface, None)
    }
    #[cfg(feature = "cpu")]
    pub(crate) fn boundary_for_role(
        phase: EntryPhase,
        code: impl ToString,
        interface: &super::Interface,
        role: Option<&str>,
    ) -> Self {
        let mut error = Self::new(phase, code);
        if let Some(r) = interface
            .outstanding_requirements()
            .iter()
            .find(|r| role.is_none_or(|role| r.role == role))
        {
            error.path = Some(format!(
                "{}[{}].path{:?}@{}:{}",
                if r.output { "outputs" } else { "inputs" },
                r.port,
                r.path,
                r.role,
                r.reason
            ));
        }
        error
    }
    #[cfg(feature = "cpu")]
    pub(crate) fn input(error: super::inputs::InputError) -> Self {
        Self {
            phase: EntryPhase::Request,
            code: error.code,
            path: Some(error.path),
        }
    }
    /// Schema location for a document refusal, if the source supplied one.
    pub fn path(&self) -> Option<&str> {
        self.path.as_deref()
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
#[cfg(feature = "cpu")]
pub(super) type EntryResult<T> = Result<T, EntryError>;

impl From<super::PackageError> for EntryError {
    fn from(error: super::PackageError) -> Self {
        Self::new(EntryPhase::Package, error)
    }
}
