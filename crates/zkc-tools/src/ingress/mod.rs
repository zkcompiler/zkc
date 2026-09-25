//! Bounded native preparation, not a security judgment. Expected descriptors
//! come from authenticated compiler/application configuration. Native decoders,
//! arithmetic and cryptographic libraries remain trusted under their contracts.
//! Success values retain immutable actual payloads; no API reopens input paths.
mod groth16;
mod index;
use crate::groth16::PreparedRelation;
pub use groth16::*;
pub use index::*;
use std::sync::Arc;

/// Exact owner-normalized subject. This is configuration, not evidence.
#[derive(Clone, Debug)]
pub struct RelationSubject(Arc<PreparedRelation>);
impl RelationSubject {
    pub fn from_normalized(expected: &[u8]) -> Result<Self> {
        Ok(Self(Arc::new(
            PreparedRelation::from_normalized(expected).map_err(relation_error)?,
        )))
    }
    pub fn from_prepared(expected: &PreparedRelation) -> Self {
        Self(Arc::new(expected.clone()))
    }
    pub fn descriptor(&self) -> &[u8] {
        self.0.canonical_descriptor()
    }
    pub fn relation(&self) -> &PreparedRelation {
        &self.0
    }
}
impl PartialEq for RelationSubject {
    fn eq(&self, other: &Self) -> bool {
        self.descriptor() == other.descriptor()
    }
}
impl Eq for RelationSubject {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FailureKind {
    Mismatch,
    Malformed,
    Resource,
    Unavailable,
    UnapprovedPremise,
    Execution,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Failure {
    pub kind: FailureKind,
    pub code: &'static str,
    pub detail: String,
}
impl std::fmt::Display for Failure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ({:?}): {}", self.code, self.kind, self.detail)
    }
}
impl std::error::Error for Failure {}
pub type Result<T> = std::result::Result<T, Failure>;
fn fail(kind: FailureKind, code: &'static str) -> Failure {
    Failure {
        kind,
        code,
        detail: String::new(),
    }
}
fn execution_error(e: crate::groth16::Error) -> Failure {
    Failure {
        kind: FailureKind::Execution,
        code: e.code,
        detail: e.detail,
    }
}
fn relation_error(e: crate::groth16::Error) -> Failure {
    let kind = match e.code {
        "groth16-relation-limit" | "groth16-relation-resource" => FailureKind::Resource,
        _ => FailureKind::Malformed,
    };
    fail(kind, e.code)
}
fn import_error(e: crate::snarkjs::Error) -> Failure {
    let kind = match e.0 {
        "import-file-limit"
        | "import-variable-limit"
        | "import-coefficient-limit"
        | "import-decoded-limit"
        | "import-size-overflow"
        | "import-allocation"
        | "import-element-policy"
        | "import-value-policy"
        | "import-matrix-policy"
        | "import-domain-limit" => FailureKind::Resource,
        _ => FailureKind::Malformed,
    };
    fail(kind, e.0)
}
fn pcs_error(e: zkc_arkworks::Error) -> Failure {
    use zkc_arkworks::Error::*;
    let kind = match e {
        ArityLimit | ElementLimit | ByteLimit | SetupLimit | CapacityOverflow | Allocation => {
            FailureKind::Resource
        }
        KeyMismatch | ArityMismatch { .. } => FailureKind::Mismatch,
        _ => FailureKind::Malformed,
    };
    fail(kind, e.code())
}

/// Fixed missing predicates; accepting one never constructs checked evidence.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Premise {
    Groth16CDerivation,
    Groth16IcDerivation,
    Groth16HDerivation,
    Groth16QueryConsistency,
    Ceremony,
    NativeCryptoContracts,
    PcsBasisConsistency,
}
#[derive(Clone, Debug, Default)]
pub struct AcceptedPremises(std::collections::BTreeSet<Premise>);
impl AcceptedPremises {
    pub fn new(premises: impl IntoIterator<Item = Premise>) -> Self {
        Self(premises.into_iter().collect())
    }
    pub fn contains(&self, premise: Premise) -> bool {
        self.0.contains(&premise)
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Predicate {
    Groth16RelationLayoutAndAB,
    ExpectedVerificationKey,
    KeyShapeAndDomain,
    AssignmentLayoutAndPublicPrefix,
    PcsMaterialAndCapacity,
    MatrixCoefficientEncoding,
}
/// Read-only diagnostic reports are not transferable evidence capabilities.
/// Consumers must use the private-constructor checked material itself.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EvidenceStatus {
    Checked(Predicate),
    AcceptedPremise(Premise),
    /// This validator establishes no proof of the named predicate.
    MissingProof(Premise),
    /// The current invocation has not accepted this external premise.
    UnacceptedPremise(Premise),
}

fn authorize(
    required: impl IntoIterator<Item = Premise>,
    accepted: &AcceptedPremises,
) -> Result<()> {
    if required.into_iter().any(|p| !accepted.contains(p)) {
        return Err(fail(
            FailureKind::UnapprovedPremise,
            "ingress-required-premise",
        ));
    }
    Ok(())
}
