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
    AcceptanceGuard,
    Conjunction,
    SourceHistory,
    ManagedHistory,
    Mathematical(&'static str),
    History {
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
pub struct Catalog {
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
}
