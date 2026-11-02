//! Static projections of the shared declaration schema. Strings here are atomic
//! nominal names, never encoded types, signatures, expressions or execution IR.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Domain(&'static str),
    Type,
    Nat,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Custody {
    PublicValue,
    PrivateImmutable,
    Affine,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TypeConstructor {
    pub name: &'static str,
    pub parameters: &'static [Kind],
    pub copy: bool,
    pub drop: bool,
    pub custody: Custody,
    pub native_local: bool,
    pub mathematical: bool,
    pub participants: bool,
    pub constructible: bool,
    pub message: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Capability {
    pub name: &'static str,
    pub parameters: &'static [Kind],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Member {
    pub name: &'static str,
    pub owner: Kind,
    pub result: Kind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rule {
    pub premise: &'static str,
    pub conclusion: &'static str,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Family {
    pub family: &'static str,
    pub element: &'static str,
    pub result: &'static str,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AssociatedType {
    pub sort: &'static str,
    pub member: &'static str,
    pub constructor: &'static str,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExportTarget {
    Constructor(&'static str),
    Predicate(&'static str),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Export {
    pub module: &'static str,
    pub name: &'static str,
    pub target: ExportTarget,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Term {
    Root {
        name: &'static str,
        parameter: Kind,
    },
    Project {
        member: &'static str,
        parent: usize,
    },
    Apply {
        constructor: &'static str,
        arguments: &'static [usize],
    },
    Natural(u64),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Port {
    Term(usize),
    Apply {
        constructor: &'static str,
        arguments: &'static [usize],
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NumericalResult {
    Map,
    Sum,
    Product,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Signature {
    Fixed {
        inputs: &'static [Port],
        outputs: &'static [Port],
    },
    Numerical {
        field: usize,
        result: NumericalResult,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Requirement {
    pub capability: &'static str,
    pub arguments: &'static [usize],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stage {
    Source,
    Construction,
    CompilerGenerated,
    Physical,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParameterValidator {
    None,
    Natural,
    Extent,
    FieldLiteral,
    FieldLiterals,
    MatrixShape,
    MatrixIdentity,
    AssetIdentity,
    MatrixVector,
    GatherIndices,
    ScatterIndices,
    NumericalExpression,
    NativeOrigin,
    NativeIndexBlock,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Parameters {
    pub validator: ParameterValidator,
    pub minimum: usize,
    pub maximum: Option<usize>,
    pub field: Option<usize>,
    pub asset_format: Option<&'static str>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SamplingProvider {
    Entropy,
    Transcript,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SamplingDomain {
    Field,
    FieldVector,
    BoundedIndex,
    IndexBlock,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DomainValueRule {
    Constant { parameter: usize },
    Length { input: usize },
    Multiply { input: usize, other: usize },
    Divide { input: usize, other: usize },
}

/// Roles index logical data ports, excluding scope and outcome administration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Facet {
    PublicReplay,
    /// Equal complete logical inputs/parameters have equal normal results or
    /// the same logical stop under an installed exact admitted interpretation.
    /// Does not imply totality, speculation, budget equality or private service
    /// authority. Selected implementations need their own interpretation;
    /// callers still check exact bindings, closed functions and recursive data.
    DeterministicData,
    AcceptanceGuard,
    Conjunction,
    SourceHistory,
    ManagedHistory,
    Mathematical(&'static str),
    History {
        state_input: usize,
        state_output: usize,
    },
    /// Output `state_output` is the identity successor of the exact resource
    /// received at input `state_input`: the same `resource_unit` type and Slot,
    /// neither duplicated nor dropped. Grants no value equality, purity,
    /// reordering or speculation.
    Succession {
        state_input: usize,
        state_output: usize,
    },
    Observation {
        state_input: usize,
        payload_input: usize,
        state_output: usize,
    },
    Sampling {
        provider: SamplingProvider,
        domain: SamplingDomain,
        state_input: usize,
        value_output: usize,
        state_output: usize,
        bound_input: Option<usize>,
    },
    Diagonal {
        factors_input: usize,
        values_input: usize,
        result_output: usize,
    },
    Contraction {
        coefficients_input: usize,
        values_input: usize,
    },
    Coset {
        shift_input: usize,
        size_input: usize,
        size_is_length: bool,
        folded_output: bool,
        vector_output: Option<usize>,
    },
    DomainValue {
        rule: DomainValueRule,
        output: usize,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Operation {
    pub name: &'static str,
    pub scope: &'static [Term],
    pub stage: Stage,
    pub parameters: Parameters,
    pub signature: Signature,
    pub requirements: &'static [Requirement],
    pub facets: &'static [Facet],
    pub derived_counterpart: Option<&'static str>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConsumerImplementation {
    Unselected,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ConsumerProfileOperation {
    pub operation: &'static str,
    /// Formal roots only, in declaration scope order.
    pub static_parameters: &'static [Kind],
}

/// Generation checks each entry's exact declaration expectation before
/// publishing these references. Membership supplies no execution or proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ConsumerProfile {
    pub name: &'static str,
    pub implementation: ConsumerImplementation,
    pub type_constructors: &'static [&'static str],
    pub parameter_validators: &'static [ParameterValidator],
    pub operations: &'static [ConsumerProfileOperation],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Algebra {
    FieldRing,
    GroupModule,
    Access,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MathematicalSignature {
    FieldConstant,
    FieldBinary,
    GroupBinary,
    GroupAction,
    ElementAccess,
    MatrixAccess,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Identity {
    None,
    Zero,
    One,
    GroupIdentity,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Access {
    None,
    Element,
    MatrixCell,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Laws {
    pub algebra: Algebra,
    pub signature: MathematicalSignature,
    pub associative: bool,
    pub commutative: bool,
    pub total: bool,
    pub left_identity: Identity,
    pub right_identity: Identity,
    pub annihilator: Identity,
    pub scalar_action: bool,
    pub access: Access,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MathematicalIdentity {
    pub name: &'static str,
    pub laws: Option<Laws>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntrinsicDomain {
    Boolean,
    Index,
    Collection,
    Field,
    Group,
    Quotient,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Intrinsic {
    pub name: &'static str,
    pub identity: &'static str,
    pub domain: IntrinsicDomain,
    pub naturals: usize,
    pub domain_points: bool,
    pub scalar: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceDeclarationKind {
    Math,
    Local,
    Interface,
}
/// A source declaration type: a static parameter, optionally its associated
/// member, or a parameterless constructor.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceTerm {
    Static {
        index: usize,
        member: Option<&'static str>,
    },
    Constructor(&'static str),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceStatic {
    pub name: &'static str,
    pub kind: Kind,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceInput {
    pub name: &'static str,
    pub term: SourceTerm,
}
/// Exactly one association: a primitive mathematical intrinsic or operation,
/// or a declared frontend rule. No backend or formal authority is installed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FrontendAssociation {
    Primitive(&'static str),
    Rule(&'static str),
}
/// One installed source declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FrontendDeclaration {
    pub identity: &'static str,
    pub owner: &'static str,
    pub name: &'static str,
    pub kind: SourceDeclarationKind,
    pub statics: &'static [SourceStatic],
    pub inputs: &'static [SourceInput],
    pub output: Option<SourceTerm>,
    pub association: FrontendAssociation,
    pub implicit: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NotationAssociativity {
    Left,
    Right,
    None,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NotationFixity {
    pub associativity: NotationAssociativity,
    pub precedence: usize,
}
/// An installed notation of a declaration of its owner.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FrontendNotation {
    pub owner: &'static str,
    pub symbol: &'static str,
    pub fixity: Option<NotationFixity>,
    pub target: &'static str,
    pub public: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FrontendHome {
    pub members: &'static [&'static str],
    pub constructor: &'static str,
    pub module: &'static str,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ServiceSignature {
    RandomDraw,
    RandomIndex,
    RandomIndices,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ServiceMethodDeclaration {
    pub name: &'static str,
    pub signature: ServiceSignature,
    pub capability: &'static str,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Catalog {
    pub frontend_declarations: &'static [FrontendDeclaration],
    pub frontend_notations: &'static [FrontendNotation],
    pub frontend_homes: &'static [FrontendHome],
    pub service_methods: &'static [ServiceMethodDeclaration],
    pub sorts: &'static [&'static str],
    pub types: &'static [TypeConstructor],
    pub operations: &'static [Operation],
    pub members: &'static [Member],
    pub rules: &'static [Rule],
    pub capabilities: &'static [Capability],
    pub exports: &'static [Export],
    pub families: &'static [Family],
    pub associated_types: &'static [AssociatedType],
    pub mathematical_identities: &'static [MathematicalIdentity],
    pub mathematical_intrinsics: &'static [Intrinsic],
    pub consumer_profiles: &'static [ConsumerProfile],
    pub domains: &'static [InstalledDomain],
    pub logical_types: &'static [LogicalTypeInstance],
    pub frame_tags: &'static [FrameTag],
    pub codecs: &'static [Codec],
    pub aggregate_frames: &'static [AggregateFrame],
    pub random_services: &'static [RandomService],
    pub limits: &'static [Limit],
    pub finite_definitions: &'static [FiniteDefinition],
    pub domain_constructors: &'static [DomainConstructor],
}

// Installed instances of `zkc.contract-declarations/0`: which nominal domains,
// logical type instances, codecs and frames exist. A row grants no execution,
// transport or implementation authority; a target admits its own handlers.

/// One installed nominal domain. Members are ordered `(member, identity)` pairs
/// and capabilities keep their declared order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InstalledDomain {
    pub identity: crate::DomainIdentity,
    pub sort: &'static str,
    pub members: &'static [(&'static str, crate::DomainIdentity)],
    pub capabilities: &'static [&'static str],
    pub facts: DomainFacts,
}
/// The sort-specific facts: Field, Transcript and Commitment rows have them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DomainFacts {
    None,
    Field(FieldFacts),
    Transcript(TranscriptFacts),
    Commitment(CommitmentFacts),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FieldFacts {
    /// The characteristic as a canonical decimal.
    pub characteristic: &'static str,
    pub structure: FieldStructure,
    pub two_adic: Option<TwoAdicConvention>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExtensionBase {
    BaseField,
    PrimeSubfield,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FieldStructure {
    Prime,
    /// `B[X]/(X^degree - sum(c * X^e))` over the named base, with the
    /// `(e, c)` terms in strictly decreasing exponent order.
    Extension {
        over: ExtensionBase,
        degree: usize,
        reduction: &'static [(usize, &'static str)],
    },
}
/// A prime field's coset convention; cosets list `shift * root^i` in order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TwoAdicConvention {
    pub convention: &'static str,
    pub maximal_root: &'static str,
    pub two_adicity: usize,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TranscriptFamily {
    Merlin3,
    Spongefish080,
    HashChain,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ByteHash {
    Keccak256,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChallengeDecoder {
    Fr64Be,
    Rejection31Le,
    Rejection64Le,
    Scalar64Le,
}
/// Typed facts about the transcript algorithm that `family` names.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TranscriptFacts {
    pub family: TranscriptFamily,
    pub hash: Option<ByteHash>,
    pub decoder: ChallengeDecoder,
    pub binds_suite: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CommitmentScheme {
    Keccak256Rows,
    Poseidon2Rows,
    MultilinearKzg,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CommitmentFacts {
    Keccak256Rows {
        digest_bytes: usize,
    },
    Poseidon2Rows {
        permutation: &'static str,
        digest_bytes: usize,
        digest_word_bytes: usize,
    },
    MultilinearKzg,
}
impl CommitmentFacts {
    pub fn scheme(self) -> CommitmentScheme {
        match self {
            Self::Keccak256Rows { .. } => CommitmentScheme::Keccak256Rows,
            Self::Poseidon2Rows { .. } => CommitmentScheme::Poseidon2Rows,
            Self::MultilinearKzg => CommitmentScheme::MultilinearKzg,
        }
    }
}
/// An admitted instance of a nullary or unary constructor.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LogicalTypeInstance {
    pub kind: &'static str,
    pub domain: Option<crate::DomainIdentity>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FrameLayout {
    Scalar,
    Vector,
    SparseMatrix,
    MerkleRoot,
    MerklePath,
    DigestRoot,
    DigestProof,
    PcsCommitment,
    PcsProof,
    Table,
    Sequence,
    Variant,
    FieldArray,
}
/// The codecs of `kind` over commitments of `scheme` share the tag.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SharedFrame {
    pub kind: &'static str,
    pub scheme: CommitmentScheme,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FrameTag {
    pub tag: u8,
    pub layout: FrameLayout,
    pub shared: Option<SharedFrame>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CodecFrame {
    pub tag: u8,
    pub element_bytes: Option<usize>,
    pub bytes: Option<usize>,
    pub bytes_per_arity: Option<usize>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Codec {
    pub identity: &'static str,
    pub kind: &'static str,
    pub domain: Option<crate::DomainIdentity>,
    pub frame: Option<CodecFrame>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AggregateFrame {
    pub constructor: &'static str,
    pub domain: Option<crate::DomainIdentity>,
    pub tag: u8,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RandomService {
    pub contract: &'static str,
    pub field: crate::DomainIdentity,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LimitUnit {
    Roles,
    Bytes,
    Elements,
    Entries,
    Steps,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LimitPhase {
    Formation,
    Admission,
    Publication,
    Execution,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limit {
    pub name: &'static str,
    pub value: u64,
    pub unit: LimitUnit,
    pub owner: &'static str,
    pub scope: &'static str,
    pub phase: LimitPhase,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FiniteMode {
    Math,
    Local,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FiniteOperation {
    Fold,
    Collect,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FiniteDefinition {
    pub identity: &'static str,
    pub mode: FiniteMode,
    pub operation: FiniteOperation,
    pub collection: Option<&'static str>,
    pub filtered: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DomainConstructorKind {
    Elements,
    Indices,
    Range,
    Zip,
    Product,
    MatrixRow,
    MatrixColumn,
    MatrixCoordinates,
    SourceArray,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DomainConstructor {
    pub identity: &'static str,
    pub kind: DomainConstructorKind,
    pub axis: usize,
}

// Available physical choices of `zkc.native-installation/0`. A preference is
// not an installation grant: a target still admits each exact handler,
// signature and storage owner.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValueFrame {
    Canonical,
    Local,
}
/// The implementation family that a binding selects.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Provider {
    Arkworks,
    Blst,
    Dalek,
    Halo2curvesAxiom,
    Plonky3,
    Spongefish,
}
impl Provider {
    pub fn name(self) -> &'static str {
        match self {
            Self::Arkworks => "arkworks",
            Self::Blst => "blst",
            Self::Dalek => "dalek",
            Self::Halo2curvesAxiom => "halo2curves-axiom",
            Self::Plonky3 => "plonky3",
            Self::Spongefish => "spongefish",
        }
    }
}
/// The native library contribution that owns storage and handlers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InstallationUnit {
    Arkworks,
    Blst,
    Dalek,
    Halo2curves,
    Plonky3,
    Independent,
}
impl InstallationUnit {
    pub fn name(self) -> &'static str {
        match self {
            Self::Arkworks => "arkworks",
            Self::Blst => "blst",
            Self::Dalek => "dalek",
            Self::Halo2curves => "halo2curves",
            Self::Plonky3 => "plonky3",
            Self::Independent => "independent",
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Representation {
    pub identity: &'static str,
    pub kind: &'static str,
    pub domain: Option<crate::DomainIdentity>,
    pub default: bool,
    pub layout: Option<&'static str>,
    pub frame: ValueFrame,
    pub unit: InstallationUnit,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArgumentPattern {
    Any,
    Domain(crate::DomainIdentity),
    /// An exact admitted logical type instance.
    Type(LogicalTypeInstance),
    Naturals {
        minimum: u64,
        maximum: u64,
    },
}
/// The key of one representation row.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RepresentationReference {
    pub kind: &'static str,
    pub domain: Option<crate::DomainIdentity>,
    pub representation: &'static str,
}
/// A dense container has a `child`, a `provider` and a `vector_port`: the
/// provider's dense operations use this container and exchange vectors in the
/// port's representation, a calling convention of the installation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AppliedRepresentation {
    pub constructor: &'static str,
    pub arguments: &'static [ArgumentPattern],
    pub identity: &'static str,
    pub default: bool,
    pub child: Option<RepresentationReference>,
    pub frame: ValueFrame,
    pub provider: Option<Provider>,
    pub unit: InstallationUnit,
    pub vector_port: Option<RepresentationReference>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProviderPreference {
    pub domain: crate::DomainIdentity,
    pub default: Provider,
    pub alternatives: &'static [Provider],
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProviderUnit {
    pub provider: Provider,
    pub unit: InstallationUnit,
}
/// Canonical residue arithmetic in the field's default representation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ResidueArithmetic {
    pub representation: &'static str,
}
/// Coordinates stored as `x * 2^radix_bits mod characteristic`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MontgomeryForm {
    pub word_bytes: usize,
    pub radix_bits: usize,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ByteOrder {
    LittleEndian,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ByteEncoding {
    pub codec: &'static str,
    pub order: ByteOrder,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FieldForm {
    pub field: crate::DomainIdentity,
    pub arithmetic: Option<ResidueArithmetic>,
    pub montgomery: Option<MontgomeryForm>,
    pub byte_encoding: Option<ByteEncoding>,
}
/// A backend calling convention, not part of the logical declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PhysicalArguments {
    pub operation: &'static str,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Installation {
    pub representations: &'static [Representation],
    pub applied_representations: &'static [AppliedRepresentation],
    pub providers: &'static [ProviderPreference],
    pub provider_units: &'static [ProviderUnit],
    pub field_forms: &'static [FieldForm],
    pub physical_arguments: &'static [PhysicalArguments],
}
