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

/// Operation port shapes. Nominal instantiation is a separate check;
/// this table does not authorize a physical implementation.
pub(crate) fn operation_shape(name: &str) -> Option<KernelSignature> {
    use Type::*;
    if let Some(kind) = name.strip_prefix("transcript.observe.") {
        let ty = Type::parse_kind(kind).ok()?;
        return ty.is_serializable().then(|| KernelSignature {
            inputs: vec![Transcript, ty],
            outputs: vec![Transcript],
            attributes: AttributeRule::MessageOrigin,
        });
    }
    let (inputs, outputs, attributes): (&[Type], &[Type], AttributeRule) = match name {
        "oracle.commit" => (
            &[Vector, Index],
            &[Commitment, OpeningState],
            AttributeRule::None,
        ),
        "oracle.open" => (
            &[OpeningState, Index],
            &[Vector, Proof],
            AttributeRule::None,
        ),
        "oracle.check" => (
            &[Commitment, Index, Index, Index, Vector, Proof],
            &[Bool],
            AttributeRule::None,
        ),
        "commitments.empty" => (&[], &[Commitments], AttributeRule::None),
        "commitments.append" => (
            &[Commitments, Commitment],
            &[Commitments],
            AttributeRule::None,
        ),
        "commitments.at" => (&[Commitments, Index], &[Commitment], AttributeRule::None),
        "commitments.length" => (&[Commitments], &[Index], AttributeRule::None),
        "opening_states.empty" => (&[], &[OpeningStates], AttributeRule::None),
        "opening_states.append" => (
            &[OpeningStates, OpeningState],
            &[OpeningStates],
            AttributeRule::None,
        ),
        "opening_states.at" => (
            &[OpeningStates, Index],
            &[OpeningState],
            AttributeRule::None,
        ),
        "opening_states.length" => (&[OpeningStates], &[Index], AttributeRule::None),
        "index.constant" => (&[], &[Index], AttributeRule::Unsigned64),
        "index.add" | "index.sub" | "index.mul" | "index.div" | "index.mod" => {
            (&[Index, Index], &[Index], AttributeRule::None)
        }
        "index.equal" | "index.less" => (&[Index, Index], &[Bool], AttributeRule::None),
        "external.monero.init" => (&[Indices], &[Indices], AttributeRule::None),
        "external.monero.hash" => (&[Indices], &[Indices], AttributeRule::None),
        "external.monero.update" => (
            &[Indices, Indices],
            &[Indices, Indices],
            AttributeRule::None,
        ),
        "external.openvm.init" => (&[], &[Indices], AttributeRule::None),
        "external.openvm.observe" => (&[Indices, Indices], &[Indices], AttributeRule::None),
        "external.openvm.sample" => (&[Indices], &[Indices, Index], AttributeRule::None),
        "external.openvm.sample_ext" => (&[Indices], &[Indices, Indices], AttributeRule::None),
        "external.openvm.sample_bits" => {
            (&[Indices, Index], &[Indices, Index], AttributeRule::None)
        }
        "external.openvm.check_witness" => (
            &[Indices, Index, Index],
            &[Indices, Bool],
            AttributeRule::None,
        ),
        "indices.empty" => (&[], &[Indices], AttributeRule::None),
        "indices.append" => (&[Indices, Index], &[Indices], AttributeRule::None),
        "indices.at" => (&[Indices, Index], &[Index], AttributeRule::None),
        "indices.length" => (&[Indices], &[Index], AttributeRule::None),
        "vector.get" => (&[Vector, Index], &[Field], AttributeRule::None),
        "vector.slice" => (&[Vector, Index, Index], &[Vector], AttributeRule::None),
        "vector.length" => (&[Vector], &[Index], AttributeRule::None),
        "vector.rotate" => (&[Vector, Index], &[Vector], AttributeRule::None),
        "vector.interleave" => (&[Vector, Vector], &[Vector], AttributeRule::None),
        "vector.prefix_product" => (&[Vector], &[Vector], AttributeRule::None),
        "vector.prefix_sum" => (&[Vector], &[Vector], AttributeRule::None),
        "vector.inverse" => (&[Vector], &[Vector], AttributeRule::None),
        "vector.embed" => (&[Vector], &[Vector], AttributeRule::None),
        "vector.fill" => (&[Field, Index], &[Vector], AttributeRule::None),
        "vector.geometric" => (&[Field, Index], &[Vector], AttributeRule::None),
        "field.from_index" => (&[Index], &[Field], AttributeRule::None),
        "poly.coefficient_count" => (&[Polynomial], &[Index], AttributeRule::None),
        "poly.coset_evaluate" => (&[Polynomial, Field, Index], &[Vector], AttributeRule::None),
        "poly.coset_interpolate" => (&[Vector, Field], &[Polynomial], AttributeRule::None),
        "poly.domain_point" => (&[Field, Index, Index], &[Field], AttributeRule::None),
        "poly.domain_root" => (&[Index], &[Field], AttributeRule::None),
        "poly.domain_points" => (&[Field, Index], &[Vector], AttributeRule::None),
        "poly.even_odd_fold" => (&[Vector, Field, Field], &[Vector], AttributeRule::None),
        "poly.divide_opening" => (
            &[Polynomial, Field, Field],
            &[Polynomial],
            AttributeRule::None,
        ),
        "poly.opening_quotient" => (
            &[Vector, Field, Field, Field],
            &[Vector],
            AttributeRule::None,
        ),
        "field.sub" => (&[Field, Field], &[Field], AttributeRule::None),
        "field.neg" | "field.inverse" | "field.embed" => (&[Field], &[Field], AttributeRule::None),
        "matrix.mul_vector" | "matrix.transpose_mul_vector" => {
            (&[Matrix, Vector], &[Vector], AttributeRule::None)
        }
        "matrix.bilinear" => (&[Matrix, Vector, Vector], &[Field], AttributeRule::None),
        "matrix.identity_check" => (&[Matrix], &[Bool], AttributeRule::MatrixIdentity),
        "matrix.shape_check" => (&[Matrix], &[Bool], AttributeRule::MatrixDimensions),
        "vector.constant" => (&[], &[Vector], AttributeRule::FieldDecimals),
        "vector.scatter_sum" => (&[Vector], &[Vector], AttributeRule::ScatterShape),
        "vector.empty" => (&[], &[Vector], AttributeRule::None),
        "vector.append" => (&[Vector, Field], &[Vector], AttributeRule::None),
        "vector.splat" | "vector.powers" => (&[Field], &[Vector], AttributeRule::NaturalIndex),
        "vector.add" | "vector.sub" | "vector.mul" | "vector.concat" | "vector.kronecker" => {
            (&[Vector, Vector], &[Vector], AttributeRule::None)
        }
        "vector.scale" => (&[Vector, Field], &[Vector], AttributeRule::None),
        "vector.sum" => (&[Vector], &[Field], AttributeRule::None),
        "vector.dot" => (&[Vector, Vector], &[Field], AttributeRule::None),
        "vector.split" => (&[Vector], &[Vector, Vector], AttributeRule::None),
        "vector.at" => (&[Vector], &[Field], AttributeRule::NaturalIndex),
        "vector.length_check" => (&[Vector], &[Bool], AttributeRule::NaturalIndex),
        "vector.gather" => (&[Vector], &[Vector], AttributeRule::NaturalIndices),
        "vector.matvec" => (&[Vector, Vector], &[Vector], AttributeRule::MatrixShape),
        "vector.from_point" | "poly.equality_weights" => (&[Point], &[Vector], AttributeRule::None),
        "vector.to_point" => (&[Vector], &[Point], AttributeRule::None),
        "vector.from_table" => (&[Table], &[Vector], AttributeRule::None),
        "vector.to_table" => (&[Vector], &[Table], AttributeRule::None),
        "poly.from_coefficients" => (&[Vector], &[Polynomial], AttributeRule::None),
        "poly.coefficients" => (&[Polynomial], &[Vector], AttributeRule::None),
        "poly.degree_check" => (&[Polynomial], &[Bool], AttributeRule::NaturalIndex),
        "poly.univariate_evaluate" => (&[Polynomial, Field], &[Field], AttributeRule::None),
        "poly.univariate_boundary" => (&[Polynomial], &[Field], AttributeRule::None),
        "random.vector" => (&[Rng], &[Vector, Rng], AttributeRule::NaturalIndex),
        "curve.neg" => (&[Group], &[Group], AttributeRule::None),
        "curve.nonidentity" => (&[Group], &[Bool], AttributeRule::None),
        "curve.msm" => (&[Vector, Groups], &[Group], AttributeRule::None),
        "curve.scale_each" => (&[Vector, Groups], &[Groups], AttributeRule::None),
        "curve.vector_add" | "curve.concat" => (&[Groups, Groups], &[Groups], AttributeRule::None),
        "curve.vector_scale" => (&[Groups, Field], &[Groups], AttributeRule::None),
        "curve.split" => (&[Groups], &[Groups, Groups], AttributeRule::None),
        "pairing.check" => (&[Groups, Groups], &[Bool], AttributeRule::None),
        "field.constant" => (&[], &[Field], AttributeRule::FieldDecimal),
        "field.add" | "field.mul" => (&[Field, Field], &[Field], AttributeRule::None),
        "field.equal" => (&[Field, Field], &[Bool], AttributeRule::None),
        "bool.and" | "bool.or" => (&[Bool, Bool], &[Bool], AttributeRule::None),
        "bool.not" => (&[Bool], &[Bool], AttributeRule::None),
        "control.require" => (&[Bool], &[], AttributeRule::None),
        "poly.product_sum" => (&[Table, Table], &[Field], AttributeRule::None),
        "poly.product_round" => (&[Table, Table], &[Round], AttributeRule::None),
        "poly.boundary" => (&[Round], &[Field], AttributeRule::None),
        "poly.round_evaluate" => (&[Round, Field], &[Field], AttributeRule::None),
        "poly.fold" => (&[Table, Field], &[Table], AttributeRule::None),
        "poly.evaluate" => (&[Table, Point], &[Field], AttributeRule::None),
        "poly.empty_point" => (&[], &[Point], AttributeRule::None),
        "poly.append_point" => (&[Point, Field], &[Point], AttributeRule::None),
        "pcs.commit" => (
            &[ProverKey, Table],
            &[Commitment, OpeningState],
            AttributeRule::None,
        ),
        "pcs.open" => (&[OpeningState, Point], &[Field, Proof], AttributeRule::None),
        "pcs.check" => (
            &[VerifierKey, Commitment, Point, Field, Proof],
            &[Bool],
            AttributeRule::None,
        ),
        "pcs.equal" => (&[Commitment, Commitment], &[Bool], AttributeRule::None),
        "curve.generator" => (&[], &[Group], AttributeRule::None),
        "curve.add" => (&[Group, Group], &[Group], AttributeRule::None),
        "curve.scale" => (&[Group, Field], &[Group], AttributeRule::None),
        "curve.equal" => (&[Group, Group], &[Bool], AttributeRule::None),
        "curve.empty" => (&[], &[Groups], AttributeRule::None),
        "curve.append" => (&[Groups, Group], &[Groups], AttributeRule::None),
        "curve.at" => (&[Groups], &[Group], AttributeRule::NaturalIndex),
        "curve.get" => (&[Groups, Index], &[Group], AttributeRule::None),
        "curve.length" => (&[Groups], &[Index], AttributeRule::None),
        "curve.commit" => (&[Groups, Nonce], &[Groups, Nonce], AttributeRule::None),
        "curve.response" => (&[Field, Field, Nonce], &[Field], AttributeRule::None),
        "transcript.challenge" => (
            &[Transcript],
            &[Field, Transcript],
            AttributeRule::ChallengeOrigin,
        ),
        "random.index" => (&[Rng, Index], &[Index, Rng], AttributeRule::None),
        "transcript.draw_index" => (
            &[Transcript, Index],
            &[Index, Transcript],
            AttributeRule::ChallengeOrigin,
        ),
        "random.draw" => (&[Rng], &[Field, Rng], AttributeRule::None),
        _ => return None,
    };
    Some(KernelSignature {
        inputs: inputs.to_vec(),
        outputs: outputs.to_vec(),
        attributes,
    })
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
    Variant,
    ResourceUnit,
    Index,
    Indices,
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
            Self::Variant => "variant",
            Self::ResourceUnit => "resource_unit",
            Self::Index => "index",
            Self::Indices => "indices",
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
    pub fn is_affine(self) -> bool {
        match self {
            Self::Variant | Self::ResourceUnit | Self::Rng | Self::Nonce | Self::Transcript => true,
            Self::Index
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
            | Self::Groups
            | Self::OpeningStates
            | Self::ProverKey
            | Self::VerifierKey
            | Self::OpeningState => false,
        }
    }
    pub fn is_serializable(self) -> bool {
        match self {
            Self::Variant
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
    /// Local storage may be dropped independently of whether it has a wire
    /// representation. Provider state remains affine and is not releasable.
    /// Logical resource units are droppable but never duplicable.
    /// Positive permission to alias immutable local custody. Duplication and
    /// discard are independent permissions, explicitly checked here.
    /// Unknown/abstract types are rejected before a Type can be constructed.
    pub fn is_duplicable(self) -> bool {
        self != Self::ResourceUnit && self.is_discardable()
    }
    pub fn is_discardable(self) -> bool {
        match self {
            Self::ResourceUnit => true,
            Self::Variant | Self::Rng | Self::Nonce | Self::Transcript => false,
            Self::Index
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
            "resource_unit" => Self::ResourceUnit,
            "index" => Self::Index,
            "indices" => Self::Indices,
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
        write!(f, "{:?}: {}", self.code, self.detail)
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
