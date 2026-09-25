//! Consumer-selected checks over retained source, candidate and evidence bytes.
//! Implementing `Checker` is an implementation trust boundary, not a proof.

use crate::Error;

/// Selected by the consumer, independently of untrusted candidate metadata.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Realization {
    DirectLogicalPlan,
    TablePhysicalPlan,
}
impl Realization {
    pub fn name(self) -> &'static str {
        match self {
            Self::DirectLogicalPlan => "direct-logical-plan",
            Self::TablePhysicalPlan => "table-physical-plan",
        }
    }
}

/// A public entry selected by the consumer from its actual owned bindings.
/// The phase codec belongs to the installed policy; artifact metadata cannot
/// select this record. Equality does not prove the provider's transition law.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EndpointEntry {
    pub role: String,
    pub phase: serde_json::Value,
}
impl EndpointEntry {
    pub fn json(&self) -> serde_json::Value {
        serde_json::json!([self.role, self.phase])
    }
}

/// The consumer selects the installed profile. The certificate supplies only
/// evidence under that profile; it cannot choose roles, summaries or entry phases.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PhaseEvidence {
    pub profile: String,
    pub certificate: Vec<u8>,
    pub entry: Option<EndpointEntry>,
}

#[derive(Clone, Copy, Debug)]
pub struct CheckRequest<'a> {
    pub source: &'a [u8],
    pub candidate: &'a [u8],
    pub phase: Option<&'a PhaseEvidence>,
    pub realization: Realization,
}

/// Failure to establish the requested judgment is not a semantic refutation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CheckFailure {
    NotEstablished(String),
    Unsupported(String),
    UnresolvedRequirements(String),
    MalformedResponse,
    BudgetExceeded,
    Io,
    ProcessFailed,
}

impl CheckFailure {
    pub fn reason(&self) -> Error {
        Error(match self {
            Self::NotEstablished(code) if code == "unchecked-plan" => "unchecked-plan",
            Self::NotEstablished(code) if code == "phase-not-admitted" => "phase-not-admitted",
            Self::NotEstablished(_) => "check-not-established",
            Self::Unsupported(_) => "unsupported-check-policy",
            Self::UnresolvedRequirements(_) => "unresolved-check-requirements",
            Self::MalformedResponse => "malformed-checker-response",
            Self::BudgetExceeded => "checker-budget-exhausted",
            Self::Io => "checker-io-error",
            Self::ProcessFailed => "checker-process-failed",
        })
    }
}

pub trait Checker {
    /// Success establishes preservation and every requested additional check
    /// for these exact inputs, under the consumer's installed checker policy.
    fn check(&self, request: CheckRequest<'_>) -> Result<(), CheckFailure>;
}
