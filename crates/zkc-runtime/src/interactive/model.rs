use super::{ArtifactFormat, PhysicalType, ResolvedBinding};
use std::{collections::BTreeMap, fmt, sync::Arc};

/// Hard ceilings, shared by all admissions and executions. Callers cannot raise them.
pub struct Limits;
impl Limits {
    pub const ARTIFACT_BYTES: usize = 1024 * 1024;
    pub const JSON_DEPTH: usize = 64;
    pub const ARRAY_LENGTH: usize = 32_768;
    pub const PARAMETER: u64 = 1_048_576;
    pub const JSON_NODES: usize = 200_000;
    pub const STRING_BYTES: usize = 4096;
    pub const DEFINITIONS: usize = 4096;
    pub const PORTS: usize = 1024;
    /// Ordered operation parameters (for example gather indices), not SSA ports.
    /// Still bounded by the artifact byte/node ceilings and per-kernel rules.
    pub const OPERATION_ATTRIBUTES: usize = 16_384;
    pub const STATIC_INSTRUCTIONS: usize = 32_768;
    pub const BLOCK_DEPTH: usize = 64;
    pub const STACK_DEPTH: usize = 64;
    pub const LOOP_COUNT: u64 = 1_048_576;
    pub const INSTRUCTIONS: u64 = 1_000_000;
    pub const CALLS: u64 = 100_000;
    pub const ITERATIONS: u64 = 100_000;
    pub const LIVE_VALUES: usize = 16_384;
    pub const VALUE_BYTES: usize = 64 * 1024 * 1024;
    pub const TOTAL_VALUE_BYTES: usize = 256 * 1024 * 1024;
}

/// History transitions forbidden under private-tag local matching. External
/// transcript states are ordinary checked data, so their attribute rules do not
/// identify this scheduling effect. Construction and stateless hashing remain
/// available. See docs/spec/profiles/compiler/local-variants.md.
pub(crate) fn observes_or_samples_history(contract: &str) -> bool {
    contract.starts_with("transcript.")
        || matches!(
            contract,
            "external.monero.update"
                | "external.openvm.observe"
                | "external.openvm.sample"
                | "external.openvm.sample_ext"
                | "external.openvm.sample_bits"
                | "external.openvm.check_witness"
        )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    FixedVector,
    Variant,
    ResourceUnit,
    Index,
    Indices,
    Matrix,
    Vector,
    Polynomial,
    Field,
    NonzeroField,
    Table,
    Point,
    Round,
    Bool,
    Rng,
    Commitment,
    Commitments,
    OpeningStates,
    Proof,
    ProverKey,
    VerifierKey,
    OpeningState,
    Group,
    Nonce,
    Transcript,
    Groups,
}
impl Type {
    pub fn name(self) -> &'static str {
        match self {
            Self::FixedVector => "fixed_vector",
            Self::Variant => "variant",
            Self::ResourceUnit => "resource_unit",
            Self::Index => "index",
            Self::Indices => "indices",
            Self::Matrix => "matrix",
            Self::Vector => "vector",
            Self::Polynomial => "polynomial",
            Self::Field => "field",
            Self::NonzeroField => "nonzero_field",
            Self::Table => "table",
            Self::Point => "point",
            Self::Round => "round",
            Self::Bool => "bool",
            Self::Rng => "rng",
            Self::Commitments => "commitments",
            Self::OpeningStates => "opening_states",
            Self::Commitment => "commitment",
            Self::Proof => "proof",
            Self::ProverKey => "prover_key",
            Self::VerifierKey => "verifier_key",
            Self::OpeningState => "opening_state",
            Self::Group => "group",
            Self::Nonce => "nonce",
            Self::Transcript => "transcript",
            Self::Groups => "groups",
        }
    }
    /// Conservative treatment when only the constructor head is known.
    /// `FixedVector` and `Variant` return true because their arguments are absent;
    /// ground values must use `PhysicalType::is_affine` or
    /// `LogicalType::is_duplicable` to check their actual permissions.
    pub fn is_affine(self) -> bool {
        match self {
            Self::FixedVector
            | Self::Variant
            | Self::ResourceUnit
            | Self::Rng
            | Self::Nonce
            | Self::Transcript => true,
            Self::Index
            | Self::Indices
            | Self::Matrix
            | Self::Vector
            | Self::Polynomial
            | Self::Field
            | Self::NonzeroField
            | Self::Table
            | Self::Point
            | Self::Round
            | Self::Bool
            | Self::Commitment
            | Self::Commitments
            | Self::Proof
            | Self::Group
            | Self::Groups
            | Self::OpeningStates
            | Self::ProverKey
            | Self::VerifierKey
            | Self::OpeningState => false,
        }
    }
    pub fn is_serializable(self) -> bool {
        match self {
            Self::FixedVector
            | Self::Variant
            | Self::ResourceUnit
            | Self::Rng
            | Self::Nonce
            | Self::Transcript
            | Self::OpeningStates
            | Self::ProverKey
            | Self::VerifierKey
            | Self::OpeningState => false,
            Self::Index
            | Self::Indices
            | Self::Matrix
            | Self::Vector
            | Self::Polynomial
            | Self::Field
            | Self::NonzeroField
            | Self::Table
            | Self::Point
            | Self::Round
            | Self::Bool
            | Self::Commitment
            | Self::Commitments
            | Self::Proof
            | Self::Group
            | Self::Groups => true,
        }
    }
    /// Copy permission guaranteed by the constructor head alone.
    /// `FixedVector` and `Variant` conservatively return false; their complete
    /// arguments may permit copying. Use `LogicalType::is_duplicable` or
    /// `PhysicalType::is_duplicable` for ground values.
    pub fn is_duplicable(self) -> bool {
        self != Self::ResourceUnit && self.is_discardable()
    }
    /// Drop permission guaranteed by the constructor head alone.
    /// `FixedVector` and `Variant` conservatively return false; use
    /// `LogicalType::is_discardable` or `PhysicalType::is_discardable` for ground
    /// values. Local storage can be droppable without a wire codec, and logical
    /// resource units are droppable but never duplicable.
    pub fn is_discardable(self) -> bool {
        match self {
            Self::ResourceUnit => true,
            Self::FixedVector | Self::Variant | Self::Rng | Self::Nonce | Self::Transcript => false,
            Self::Index
            | Self::Indices
            | Self::Matrix
            | Self::Vector
            | Self::Polynomial
            | Self::Field
            | Self::NonzeroField
            | Self::Table
            | Self::Point
            | Self::Round
            | Self::Bool
            | Self::Commitment
            | Self::Commitments
            | Self::OpeningStates
            | Self::Proof
            | Self::ProverKey
            | Self::VerifierKey
            | Self::OpeningState
            | Self::Group
            | Self::Groups => true,
        }
    }
    pub(crate) fn parse_kind(name: &str) -> Result<Self, AdmissionError> {
        let ty = match name {
            "fixed_vector" => Self::FixedVector,
            "resource_unit" => Self::ResourceUnit,
            "index" => Self::Index,
            "indices" => Self::Indices,
            "matrix" => Self::Matrix,
            "vector" => Self::Vector,
            "polynomial" => Self::Polynomial,
            "field" => Self::Field,
            "nonzero_field" => Self::NonzeroField,
            "table" => Self::Table,
            "point" => Self::Point,
            "round" => Self::Round,
            "bool" => Self::Bool,
            "rng" => Self::Rng,
            "commitments" => Self::Commitments,
            "opening_states" => Self::OpeningStates,
            "commitment" => Self::Commitment,
            "proof" => Self::Proof,
            "prover_key" => Self::ProverKey,
            "verifier_key" => Self::VerifierKey,
            "opening_state" => Self::OpeningState,
            "group" => Self::Group,
            "nonce" => Self::Nonce,
            "transcript" => Self::Transcript,
            "groups" => Self::Groups,
            _ => {
                return Err(AdmissionError::new(
                    ErrorCode::Type,
                    "unknown or opaque executable type",
                ));
            }
        };
        Ok(ty)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AttributeRule {
    None,
    FieldDecimal,
    Bn254Decimal,
    Bn254Decimals,
    RistrettoDecimal,
    KoalaBearDecimal,
    FieldDecimals,
    RistrettoDecimals,
    KoalaBearDecimals,
    ScatterShape,
    Unsigned64,
    NaturalIndex,
    NaturalIndices,
    MatrixShape,
    MatrixDimensions,
    MatrixIdentity,
    MessageOrigin,
    ChallengeOrigin,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelSignature<T = Type> {
    pub inputs: Vec<T>,
    pub outputs: Vec<T>,
    pub attributes: AttributeRule,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorCode {
    Json,
    Limit,
    Record,
    Name,
    Natural,
    Stage,
    Type,
    /// A logical type has no installed or compatible physical representation.
    Representation,
    Symbol,
    Signature,
    Ssa,
    Site,
    Attributes,
    Capture,
    Cycle,
    Role,
    Parameters,
    Terminal,
    Backend,
    Correspondence,
}
impl ErrorCode {
    /// Stable admission category name, independent of diagnostic prose.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Json => "Json",
            Self::Limit => "Limit",
            Self::Record => "Record",
            Self::Name => "Name",
            Self::Natural => "Natural",
            Self::Stage => "Stage",
            Self::Type => "Type",
            Self::Representation => "Representation",
            Self::Symbol => "Symbol",
            Self::Signature => "Signature",
            Self::Ssa => "Ssa",
            Self::Site => "Site",
            Self::Attributes => "Attributes",
            Self::Capture => "Capture",
            Self::Cycle => "Cycle",
            Self::Role => "Role",
            Self::Parameters => "Parameters",
            Self::Terminal => "Terminal",
            Self::Backend => "Backend",
            Self::Correspondence => "Correspondence",
        }
    }
}
impl fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdmissionError {
    pub code: ErrorCode,
    pub detail: String,
}
impl AdmissionError {
    pub fn new(code: ErrorCode, detail: impl Into<String>) -> Self {
        Self {
            code,
            detail: detail.into(),
        }
    }
}
impl fmt::Display for AdmissionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.code, self.detail)
    }
}
impl std::error::Error for AdmissionError {}

pub(crate) type Ports = Vec<(String, PhysicalType)>;
pub(crate) type Body = Arc<[Instruction]>;
#[derive(Debug)]
pub(crate) struct Function {
    pub name: String,
    pub inputs: Ports,
    pub outputs: Vec<PhysicalType>,
    pub origin: LogicalOrigin,
    pub body: Arc<[LocalInstruction]>,
}
#[derive(Debug)]
pub(crate) struct MatchArm {
    pub alternative: String,
    pub payload: Vec<String>,
    pub body: Arc<[LocalInstruction]>,
}
#[derive(Debug)]
pub(crate) enum LocalInstruction {
    Variant {
        site: String,
        ty: PhysicalType,
        alternative: String,
        payload: Vec<String>,
        output: String,
    },
    Match {
        site: String,
        input: String,
        captures: Vec<String>,
        arms: Vec<MatchArm>,
        outputs: Vec<String>,
    },
    Stop {
        site: String,
        reason: String,
    },
    Conditional {
        site: String,
        condition: String,
        captures: Vec<String>,
        then_body: Arc<[LocalInstruction]>,
        else_body: Arc<[LocalInstruction]>,
        outputs: Vec<String>,
    },
    For {
        site: String,
        induction: String,
        lower: String,
        upper: String,
        carried: Vec<(String, String)>,
        captures: Vec<String>,
        body: Arc<[LocalInstruction]>,
        outputs: Vec<String>,
    },
    Yield(Vec<String>),
    Release(Vec<String>),
    Op {
        site: String,
        binding: Arc<ResolvedBinding>,
        attributes: Vec<String>,
        inputs: Vec<String>,
        outputs: Vec<String>,
    },
    Return(Vec<String>),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FamilySelector {
    pub function: String,
    pub arguments: Vec<String>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FamilyIngress {
    pub bound: u64,
    pub selectors: BTreeMap<String, FamilySelector>,
}
#[derive(Debug)]
pub(crate) enum Count {
    Constant(u64),
    Parameter(String),
}
impl Count {
    pub fn may_run(&self) -> bool {
        !matches!(self, Self::Constant(0))
    }
}
#[derive(Debug)]
pub(crate) struct Participant {
    pub symbol: String,
    pub instance: String,
    pub role: String,
    pub parameters: BTreeMap<String, u64>,
    pub families: BTreeMap<String, FamilyIngress>,
    pub inputs: Ports,
    pub outputs: Vec<PhysicalType>,
    pub body: Body,
}
#[derive(Debug)]
pub(crate) enum Instruction {
    Guard {
        site: String,
        condition: String,
    },
    Local {
        site: String,
        function: String,
        inputs: Vec<String>,
        outputs: Vec<String>,
    },
    Send {
        site: String,
        schema: String,
        peer: String,
        input: String,
    },
    Receive {
        site: String,
        schema: String,
        peer: String,
        output: String,
        ty: PhysicalType,
    },
    Call {
        site: String,
        participant: String,
        inputs: Vec<String>,
        outputs: Vec<String>,
    },
    Loop {
        site: String,
        count: Count,
        carried: Vec<(String, String)>,
        captures: Vec<String>,
        body: Body,
        outputs: Vec<String>,
    },
    Yield(Vec<String>),
    Return(Vec<String>),
    Stop {
        site: String,
        reason: String,
    },
    Incomplete {
        site: String,
    },
}
#[derive(Debug)]
pub(crate) struct Program {
    pub format: ArtifactFormat,
    pub functions: BTreeMap<String, Arc<Function>>,
    pub participants: BTreeMap<String, Arc<Participant>>,
    pub entries: BTreeMap<String, BTreeMap<String, String>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LogicalOrigin {
    pub definition: String,
    pub arguments: Vec<(String, String)>,
}

impl LocalInstruction {
    /// Visit every syntactic operation, including unreachable local regions.
    pub(crate) fn walk(body: &[Self]) -> Vec<&Self> {
        let mut out = Vec::new();
        for op in body {
            out.push(op);
            match op {
                Self::Conditional {
                    then_body,
                    else_body,
                    ..
                } => {
                    out.extend(Self::walk(then_body));
                    out.extend(Self::walk(else_body));
                }
                Self::Match { arms, .. } => {
                    for arm in arms {
                        out.extend(Self::walk(&arm.body));
                    }
                }
                Self::For { body, .. } => out.extend(Self::walk(body)),
                _ => {}
            }
        }
        out
    }
}

#[cfg(test)]
mod history_inventory {
    #[test]
    fn independent_history_classification_matches_installed_inventory() {
        let fixture = include_str!("../../../../tests/fixtures/variants/history-contracts.txt");
        let mut seen = std::collections::BTreeSet::new();
        for line in fixture.lines() {
            let (contract, expected) = line.split_once(' ').expect("inventory row");
            assert!(seen.insert(contract), "duplicate inventory contract");
            assert!(matches!(expected, "0" | "1"));
            assert_eq!(
                super::observes_or_samples_history(contract),
                expected == "1",
                "{contract}"
            );
        }
        assert!(!seen.is_empty());
    }
}
