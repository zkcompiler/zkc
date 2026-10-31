pub(crate) use super::code::{Body, Instruction, LoopCount, Participant, Ports};
use super::{PhysicalType, ResolvedBinding};
use std::{collections::BTreeMap, fmt, sync::Arc};

/// Admission and execution ceilings, plus explicitly documented policy defaults.
pub struct Limits;
impl Limits {
    pub const ARTIFACT_BYTES: usize = 4 * 1024 * 1024;
    /// Conservative installed descriptor charge across distinct physical spellings
    /// and each resolved binding signature. Parsing scratch has separate bounds.
    pub const TYPE_BYTES: usize = 64 * 1024 * 1024;
    pub const JSON_DEPTH: usize = 64;
    pub const ARRAY_LENGTH: usize = 32_768;
    pub const PARAMETER: u64 = 1_048_576;
    pub const JSON_NODES: usize = 400_000;
    pub const STRING_BYTES: usize = 4096;
    pub const DEFINITIONS: usize = 4096;
    pub const PORTS: usize = 1024;
    /// Ordered operation parameters (for example gather indices), not SSA ports.
    /// Still bounded by the artifact byte/node ceilings and per-operation rules.
    pub const OPERATION_ATTRIBUTES: usize = 16_384;
    pub const STATIC_INSTRUCTIONS: usize = 65_536;
    pub const BLOCK_DEPTH: usize = 64;
    pub const STACK_DEPTH: usize = 64;
    pub const LOOP_COUNT: u64 = 1_048_576;
    pub const INSTRUCTIONS: u64 = 1_000_000;
    pub const ITERATIONS: u64 = 100_000;
    pub const LIVE_VALUES: usize = 16_384;
    /// Hard per-value ceiling and default live-value budget.
    pub const VALUE_BYTES: usize = 64 * 1024 * 1024;
    /// Default cumulative fresh-allocation budget; callers may configure another value.
    pub const TOTAL_VALUE_BYTES: usize = 256 * 1024 * 1024;
    /// Hard and default cumulative logical-work ceiling: operand bytes read and
    /// result bytes allocated by operations and services, charged at every use.
    pub const LOGICAL_BYTES: u64 = 4 * 1024 * 1024 * 1024;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Sequence,
    FieldArray,
    FixedVector,
    Variant,
    ResourceUnit,
    Index,
    Indices,
    Bytes,
    Shake128State,
    QuotientMatrix,
    Matrix,
    Vector,
    Polynomial,
    Field,
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
            Self::Sequence => "sequence",
            Self::FieldArray => "field_array",
            Self::FixedVector => "fixed_vector",
            Self::Variant => "variant",
            Self::ResourceUnit => "resource_unit",
            Self::Index => "index",
            Self::Indices => "indices",
            Self::Bytes => "bytes",
            Self::Shake128State => "shake128_state",
            Self::QuotientMatrix => "quotient_matrix",
            Self::Matrix => "matrix",
            Self::Vector => "vector",
            Self::Polynomial => "polynomial",
            Self::Field => "field",
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
        !self.is_duplicable()
    }
    /// Wire codec availability for a nominal leaf, independently of
    /// the catalog's message-data profile and complete aggregate permissions.
    pub fn is_serializable(self) -> bool {
        match self {
            Self::QuotientMatrix
            | Self::Shake128State
            | Self::Sequence
            | Self::FieldArray
            | Self::FixedVector
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
            | Self::Bytes
            | Self::Indices
            | Self::Matrix
            | Self::Vector
            | Self::Polynomial
            | Self::Field
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
        zkc_catalog::constructor(self.name())
            .is_some_and(|row| row.copy && !row.parameters.contains(&zkc_catalog::Kind::Type))
    }
    /// Drop permission guaranteed by the constructor alone. Type parameters
    /// and variants require checking every actual child before granting it.
    pub fn is_discardable(self) -> bool {
        zkc_catalog::constructor(self.name())
            .is_some_and(|row| row.drop && !row.parameters.contains(&zkc_catalog::Kind::Type))
    }
    pub(crate) fn parse_kind(name: &str) -> Result<Self, AdmissionError> {
        let ty = match name {
            "sequence" => Self::Sequence,
            "field_array" => Self::FieldArray,
            "fixed_vector" => Self::FixedVector,
            "resource_unit" => Self::ResourceUnit,
            "index" => Self::Index,
            "indices" => Self::Indices,
            "bytes" => Self::Bytes,
            "shake128_state" => Self::Shake128State,
            "quotient_matrix" => Self::QuotientMatrix,
            "matrix" => Self::Matrix,
            "vector" => Self::Vector,
            "polynomial" => Self::Polynomial,
            "field" => Self::Field,
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
    ResidueLiteral(super::Identity),
    ResidueLiterals(super::Identity),
    Bn254Decimal,
    Bn254Decimals,
    RistrettoDecimal,
    KoalaBearDecimal,
    FieldDecimals,
    RistrettoDecimals,
    KoalaBearDecimals,
    /// Constants of a binary field: `0`, `1` or a canonical bit-pattern literal.
    Binary64Literal,
    Binary64Literals,
    Binary64Ext3Literal,
    Binary64Ext3Literals,
    ScatterShape,
    Unsigned64,
    NaturalIndex,
    NaturalIndices,
    MatrixShape,
    MatrixDimensions,
    MatrixIdentity,
    AssetIdentity,
    NativeMessageTemplate,
    NativeChallengeTemplate,
    NativeIndexTemplate,
    /// Origin, full-u64 power-of-two bound and positive block count.
    NativeIndexBlock,
    /// The same block parameters followed by the gate difficulty.
    NativeGatedIndexBlock,
    /// One canonical, exactly typed Ring body for a closed numerical binding.
    NumericalExpression,
}
/// Port types and attribute rules for an operation, including effectful ones.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OperationSignature<T = Type> {
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
    Role,
    Terminal,
    Backend,
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
            Self::Role => "Role",
            Self::Terminal => "Terminal",
            Self::Backend => "Backend",
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
    BoolConstant {
        site: String,
        output: String,
        value: bool,
    },
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
        conditional: bool,
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
#[derive(Debug)]
pub(crate) struct Model {
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
