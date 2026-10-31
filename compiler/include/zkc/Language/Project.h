#ifndef ZKC_LANGUAGE_PROJECT_H
#define ZKC_LANGUAGE_PROJECT_H

#include "zkc/Contracts/Construction.h"
#include "zkc/Contracts/Mathematical.h"
#include "zkc/Contracts/ProofFormat.h"
#include "zkc/Language/Assets.h"
#include "zkc/Language/Notation.h"
#include "zkc/Language/Types.h"
#include "zkc/Source/Source.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <variant>
#include <vector>

namespace zkc::language {
using source::Diagnostic;
using source::SourceBuffer;
using source::SourceId;
using source::SourceOrigin;
using source::Span;
struct DeclarationId {
  uint32_t index;
};
struct ValueId {
  uint32_t index;
};
struct ServiceId {
  uint32_t index;
};
class DiagnosticError : public llvm::ErrorInfo<DiagnosticError> {
public:
  static char ID;
  explicit DiagnosticError(Diagnostic diagnostic);
  const Diagnostic &diagnostic() const { return value; }
  void log(llvm::raw_ostream &) const override;
  std::error_code convertToErrorCode() const override;

private:
  Diagnostic value;
};

/// Requests may lower, but never raise, these per-invocation ceilings.
struct Limits {
  /// Every ceiling here is at least the corresponding ceiling in other.
  bool covers(const Limits &other) const;
  uint64_t files = 256, fileBytes = 1048576, captureBytes = 8388608;
  uint64_t assetBytes = 67108864, assetTotalBytes = 67108864;
  uint64_t tokens = 1000000, tokenBytes = 4096;
  uint64_t identifierBytes = 128, moduleBytes = 2048;
  // Parse depth also bounds constructed type/natural operator trees.
  uint64_t parseDepth = 64, expressionDepth = 64;
  uint64_t importDepth = 64, callDepth = 64;
  uint64_t declarations = 10000, operations = 100000, work = 8000000;
  uint64_t irBytes = 16777216, symbolBytes = 4096;
  uint64_t notationDescriptors = 4096, notationHoles = 64;
  uint64_t notationInspectionBytes = 8388608;
  uint64_t apiInspectionBytes = 8388608;
  uint64_t interfaceBytes = 4194304, locationBytes = 16777216;
  uint64_t typeDepth = 32, typeNodes = 100000, instances = 4096;
  uint64_t aggregateLeaves = 1024, naturalTerms = 1024, naturalFactors = 64;
};
llvm::Error checkLimits(const Limits &);

struct CaptureOptions {
  std::string format = "zkc";
  Limits limits;
};
enum class TokenKind {
  Word,
  Decimal,
  String,
  Punctuation,
  Whitespace,
  Comment,
  End
};
struct Token {
  TokenKind kind;
  Span span;
};
/// A logical oracle port has data at its holder and an anchor at its receivers.
/// The optional bound is a static natural for an unsized kind.
struct OraclePort {
  unsigned holder;
  std::optional<Type> maximumRows;
};
struct Port {
  std::string name;
  Type type;
  std::vector<unsigned> roles;
  Span span;
  std::optional<OraclePort> oracle = {};
};
/// A managed port is a borrowed service root, never an ordinary data type.
struct ServicePort {
  std::string name;
  Type field;
  unsigned owner;
  Span span;
  std::string contract; // Filled by selected Entry closure.
};
struct Value {
  Type type;
  /// Protocol: roster indices. Math: input dependencies. Both are sorted sets.
  std::vector<unsigned> components;
  Span span;
  /// Oracle role family: data owner, independent of sorted availability.
  std::optional<unsigned> oracleHolder = {};
};
struct MathValue {
  MathematicalIdentity identity;
  std::vector<ValueId> operands;
  std::string literal;
  std::vector<Type> staticArguments;
  std::vector<std::string> parameters;
  MathValue(MathematicalIdentity identity, std::vector<ValueId> operands,
            std::string literal, std::vector<Type> statics = {},
            std::vector<std::string> parameters = {})
      : identity(identity), operands(std::move(operands)),
        literal(std::move(literal)), staticArguments(std::move(statics)),
        parameters(std::move(parameters)) {}
};
/// A callable resolved in its definition environment. Module members retain
/// the explicit module term until ordinary entry specialization.
struct CallableReference {
  DeclarationId declaration;
  std::optional<Type> module;
};
/// The tracked Local effects, also used as fixed callback acceptance ceilings.
struct Effects {
  bool mayStop = false;
  bool opaque = false;
  bool operator!=(const Effects &other) const { return !(*this == other); }
  bool operator==(const Effects &other) const {
    return mayStop == other.mayStop && opaque == other.opaque;
  }
};
/// A union of fixed effects and bounded callback dependencies. Keys are slots
/// in the owning signature or body's static environment, never source names.
struct EffectSummary {
  Effects fixed;
  std::map<unsigned, Effects> dependencies;
  EffectSummary() = default;
  EffectSummary(Effects fixed) : fixed(fixed) {}
  bool operator==(const EffectSummary &other) const {
    return fixed == other.fixed && dependencies == other.dependencies;
  }
  bool operator!=(const EffectSummary &other) const {
    return !(*this == other);
  }
};
/// Scoped signatures are static argument contracts, never runtime Types.
struct ScopedSignature {
  enum class Mode { Math, Local } mode;
  std::vector<Type> inputs;
  Type result;
  Effects allowance;
  bool operator==(const ScopedSignature &other) const {
    return mode == other.mode && inputs == other.inputs &&
           result == other.result && allowance == other.allowance;
  }
};
struct ScopedParameter {
  std::string name;
  ScopedSignature signature;
  Span span;
  /// Source-only labels; excluded from semantic signature identity.
  std::vector<std::string> inputLabels = {};
  /// Canonical input position -> this declaration's domain formal position.
  /// Each invocation must supply the whole original item of that domain.
  std::map<unsigned, unsigned> itemOrigins = {};
};
/// Finite domains are a separate static argument category. Their ordinary
/// operands remain checked data values with authored evaluation order.
struct DomainParameter {
  std::string name;
  Type item;
  Span span;
};
struct DomainBinding {
  enum class Kind {
    Parameter,
    Application,
    Elements,
    Indices,
    Range,
    Zip,
    Product,
    MatrixRow,
    MatrixColumn,
    MatrixCoordinates,
    SourceArray
  } kind;
  Type item;
  std::vector<ValueId> operands;
  std::vector<unsigned> children;
  unsigned axis = 0;
  std::optional<unsigned> parameter = {};
  Span span = {};
  std::optional<CallableReference> factory = {};
  std::vector<Type> arguments = {};
  std::vector<unsigned> argumentOrder = {};
  /// Authored expression identity within the owning lexical declaration.
  std::optional<uint32_t> expression = {};
};
/// Closed static constructor graph. Data ports use ordinary caller operands;
/// the descriptor itself is not a runtime value or an expression interpreter.
struct DomainShape {
  std::vector<Type> inputs;
  std::vector<DomainBinding> nodes;
  unsigned result;
  std::string identity;
};
struct DomainDefinition {
  std::optional<DomainBinding::Kind> constructor;
  unsigned axis = 0;
  std::vector<DomainBinding> bindings;
  unsigned result = 0;
};
/// Static alias partition for a closed callable. Authored ports remain in the
/// ABI; input references and hidden captures select their canonical ports.
struct ClosureLayout {
  std::vector<unsigned> inputs, captures;
  bool operator==(const ClosureLayout &other) const {
    return inputs == other.inputs && captures == other.captures;
  }
};
struct ScopedInvoke {
  unsigned binding;
  std::vector<ValueId> operands;
  /// Retained authored invocation, independently checked before closure.
  uint32_t source;
};
/// A registered finite definition uses the same static environments as an
/// authored helper. Fold operands contain its initial logical state; collect
/// has no ordinary operands. Closure resolves the domain and callbacks.
struct FiniteApplication {
  enum class Kind { Fold, Collect } kind;
  unsigned domain, body;
  std::optional<unsigned> predicate;
  std::vector<ValueId> operands;
};
/// Closed finite work keeps ordinary helper calling conventions. Translation
/// supplies descriptor/item adapter ports, while capture identities remain
/// explicit values in this body's SSA space.
struct FiniteCallback {
  DeclarationId helper;
  std::vector<ValueId> captures;
};
struct FiniteComputation {
  FiniteApplication::Kind kind;
  std::shared_ptr<const DomainShape> domain;
  std::vector<ValueId> domainOperands, operands;
  FiniteCallback body;
  std::optional<FiniteCallback> predicate;
};
struct HelperCall {
  DeclarationId callee;
  std::vector<ValueId> operands;
  std::vector<Type> arguments;
  std::optional<Type> module;
  std::optional<unsigned> owner;
  std::vector<unsigned> scopedArguments = {};
  std::vector<unsigned> domainArguments = {};
};
/// A checked pointwise application of a static scalar math helper in local
/// code. Each operand is either a whole vector of the helper's field, one row
/// per element (`mapped`), or one scalar shared by every row. Row counts are
/// checked when it executes; it is not a total mathematical value.
struct BulkApplication {
  DeclarationId callee;
  std::vector<ValueId> operands;
  std::vector<Type> arguments;
  std::vector<bool> mapped;
};
struct ProtocolApplication {
  DeclarationId callee;
  std::vector<ValueId> operands;
  std::vector<Type> arguments;
  /// Caller roster indices, in the callee's declared role order.
  std::vector<unsigned> roles;
  std::vector<ServiceId> services;
};
/// A generated Host operation. Authority is supplied by the admitting Host,
/// separately from these ordinary data operands.
struct HostInvocation {
  enum class Kind { Run, Prove, Verify } kind;
  DeclarationId target;
  std::vector<Type> arguments;
  std::vector<ValueId> operands;
};
struct ServiceQuery {
  ServiceId service;
  /// Positive source domain; native constructions separately restrict it.
  std::optional<Natural> bound;
  /// Positive product-law count; present only for an indices request.
  std::optional<Natural> count = std::nullopt;
};
struct Require {
  ValueId condition;
  /// Absent in a local function, whose caller supplies its execution owner.
  std::optional<unsigned> owner;
};
struct ProtocolCompletion {
  ValueId condition;
  unsigned owner;
  /// Every owner output, in declaration order. False returns all logical
  /// values; translation supplies native successors for their affine leaves.
  std::vector<ValueId> values;
};
struct Exchange {
  unsigned sender, receiver;
  ValueId payload;
};
struct OracleSend {
  ValueId data, rows;
  unsigned holder;
  std::vector<unsigned> receivers;
  std::optional<Natural> maximum;
};
struct OracleQuery {
  ValueId handle, position;
  unsigned owner;
};
struct OracleContents {
  ValueId input;
  unsigned owner;
};
struct OracleRows {
  ValueId input;
};
struct OracleForgetRows {
  ValueId input;
};
struct OracleSequenceEmpty {
  unsigned holder;
  std::vector<unsigned> roles;
};
struct OracleSequenceAppend {
  ValueId prefix, element;
  std::vector<unsigned> roles;
};
struct OracleSequenceAt {
  ValueId input, position;
  std::vector<unsigned> roles;
};
struct OracleSequenceLength {
  ValueId input;
};
struct Restriction {
  ValueId input;
  std::vector<unsigned> roles;
};
/// Each operand supplies only its named role's component. This neither sends
/// data nor asserts equality between components.
struct RoleAssembly {
  std::vector<ValueId> operands;
  std::vector<unsigned> roles;
};
struct Body;
struct ProtocolRepeat {
  std::vector<unsigned> roles;
  ValueId count;
  Natural maximum;
  std::vector<ValueId> carried, captures;
  std::vector<ServiceId> services;
  std::shared_ptr<const Body> region;
  ClosureLayout regionLayout = {};
};
struct Construct {
  enum class Kind { Aggregate, Variant, Unpack };
  std::vector<ValueId> operands;
  std::string alternative;
  Kind kind = Kind::Aggregate;
};
struct Projection {
  ValueId input;
  std::vector<unsigned> path;
};
/// A kernel parameter position that is written from an asset term rather than
/// a literal. The closed term's identity becomes the parameter at closure.
struct AssetReference {
  unsigned position;
  Type term;
};
struct LocalPrimitive {
  /// Explicit kernel authoring retains the installed ordered envelope even
  /// when the underlying primitive also has a total mathematical spelling.
  enum class Origin { Primitive, Kernel } origin = Origin::Primitive;
  std::string contract;
  std::vector<ValueId> operands;
  std::vector<std::string> parameters;
  std::vector<Type> staticArguments;
  /// Explicit installed contract roots, independent of literal parameters.
  std::optional<std::vector<Type>> bindingArguments;
  /// Typed asset terms, closed separately from the natural static arguments.
  std::vector<AssetReference> assetReferences;
  LocalPrimitive(std::string contract, std::vector<ValueId> operands,
                 std::vector<std::string> parameters,
                 std::vector<Type> statics = {})
      : contract(std::move(contract)), operands(std::move(operands)),
        parameters(std::move(parameters)), staticArguments(std::move(statics)) {
  }
};
struct Consume {
  ValueId input;
};
struct LocalControl {
  enum class Kind { If, Match, For } kind;
  std::vector<ValueId> operands;
  std::vector<std::shared_ptr<const Body>> regions;
  std::vector<std::string> alternatives;
  unsigned carried = 0;
  std::vector<unsigned> domainArguments = {};
  std::vector<std::shared_ptr<const DomainShape>> domainShapes;
  std::vector<ClosureLayout> regionLayouts;
};
/// Source elaboration evidence retained beside the native operation. Families
/// contain canonical binding identities, not search order or implementation
/// cost.
struct CallBinding {
  CallableReference target;
  std::vector<Type> arguments;
  std::vector<ValueId> operands;
  std::string symbol;
  std::vector<std::string> family;
  std::optional<Span> origin;
  std::optional<NotationDescriptor> notation;
  /// Source occurrence and complete authored argument mapping for scoped calls.
  /// Scoped and domain indices always refer to the checked source body,
  /// including after closure erases its static binding tables from the
  /// executable body.
  std::optional<unsigned> scopedSource = {};
  std::vector<unsigned> argumentOrder = {};
  std::vector<unsigned> scopedArguments = {};
  std::vector<unsigned> domainArguments = {};
  bool filteredReduction = false;
};
struct CaptureSlot {
  uint32_t binding;
  std::vector<unsigned> path;
  Type type;
  Span firstUse;
};
struct ScopedComputation {
  DeclarationId lexicalOwner;
  uint32_t expression;
  ScopedSignature signature;
  std::vector<CaptureSlot> captures;
  std::vector<uint32_t> scopedCaptures;
  std::shared_ptr<const Body> body;
  std::vector<uint32_t> domainCaptures = {};
};
/// Parameter is an index in the body's static scoped environment. A literal
/// carries data snapshots and references to that body's scoped bindings.
struct ScopedBinding {
  ScopedSignature signature;
  std::optional<unsigned> parameter;
  std::shared_ptr<const ScopedComputation> computation;
  std::vector<ValueId> captures;
  std::vector<unsigned> scopedCaptures;
  Span span;
  std::optional<uint32_t> source;
  std::vector<unsigned> domainCaptures = {};
};
struct Operation {
  std::variant<MathValue, HelperCall, BulkApplication, Exchange, Restriction,
               RoleAssembly, Construct, Projection, LocalPrimitive, Consume,
               LocalControl, ProtocolApplication, ServiceQuery, Require,
               ProtocolRepeat, ProtocolCompletion, ScopedInvoke,
               FiniteApplication, FiniteComputation, HostInvocation, OracleSend,
               OracleQuery, OracleContents, OracleRows, OracleForgetRows,
               OracleSequenceEmpty, OracleSequenceAppend, OracleSequenceAt,
               OracleSequenceLength>
      action;
  /// Each result has its own type and participant availability.
  std::vector<ValueId> results;
  Span span;
  uint32_t statement;
  std::optional<CallBinding> binding = {};
  /// An authored selector, independent of generated operation ordinals.
  std::optional<std::string> site = {};
};
struct Body {
  enum class Mode { Math, Local, Protocol } mode;
  enum class Stage { Computation, Host } stage = Stage::Computation;
  std::vector<ServicePort> services;
  std::vector<ScopedBinding> scopedBindings;
  std::vector<DomainBinding> domainBindings;
  /// Source expression results retained for independent scoped extraction
  /// checks.
  std::map<uint32_t, ValueId> expressionValues;
  std::vector<Value> values;
  std::vector<Operation> operations;
  std::vector<ValueId> results;
  unsigned inputs = 0;
  bool stopped = false;
  std::string stopReason;
  EffectSummary effects;
  /// True when a scoped formal prevents a concrete dependency summary.
  bool parameterizedSummary = false;
  /// Includes intermediate dependencies of unused mathematical work.
  std::vector<std::vector<unsigned>> formationRequirements;
};
struct Parameter {
  enum class Sort { Type, Natural, Module, Domain, Asset, OracleKind } sort;
  std::string name, atom;
  /// Catalog sort of a Domain parameter or asset sort of an Asset parameter.
  std::string domainSort;
  Permissions permissions;
  std::optional<DeclarationId> interface;
  std::vector<Type> arguments;
  Span span;
};
struct TypeField {
  std::string name;
  Type type;
  bool isPublic = true;
  Span span;
};
struct Alternative {
  std::string name;
  std::vector<TypeField> fields;
  Span span;
};
/// A logical input subtree, selected by immutable product projections.
struct InputSelector {
  unsigned port = 0;
  std::vector<unsigned> path;
  Span span;
};
/// Preconditions on immutable callable inputs. These are distinct from static
/// natural bounds and from protocol relation clauses.
struct DataPrecondition {
  enum class Kind { IndexBound, EqualExtent } kind;
  InputSelector left, right;
  unsigned leftAxis = 0, rightAxis = 0;
  Span span;
  bool operator==(const DataPrecondition &other) const {
    return kind == other.kind && left.port == other.left.port &&
           left.path == other.left.path && right.port == other.right.port &&
           right.path == other.right.path && leftAxis == other.leftAxis &&
           rightAxis == other.rightAxis;
  }
};
struct NaturalBound {
  Natural lhs, rhs;
  Span span;
  bool inferred = false;
};
struct PermissionBound {
  Type type;
  Permissions permissions;
  Span span;
  bool inferred = false;
};
/// Boundary conditions are derived from use sites, never granted by `where`.
enum class Boundary { Participants, Construction, Message };
struct AdmissionObligation {
  Type type;
  Boundary boundary;
  Span span;
  /// Calls that transported this condition, from the original site outward.
  std::vector<Span> calls;
};
/// A catalog proposition, independent of runtime custody permissions.
struct CapabilityBound {
  std::string predicate;
  std::vector<Type> arguments;
  Span span;
  bool inferred = false;
};
enum class RelationPurpose { Parameter, Statement, Witness };
struct RelationDefinition {
  enum class Kind { Formula, Opaque, R1CS, AIR, Bundle } kind = Kind::Formula;
  std::vector<RelationPurpose> purposes;
  std::string externalKind, key, revision;
  std::optional<unsigned> asset;
};
/// A logical port component. Paths select product fields, never native
/// container elements, variant payloads or internal execution values.
struct SpecificationSelector {
  bool output = false;
  unsigned port = 0, role = 0;
  std::vector<unsigned> path;
  Span span;
  /// Select logical data through an oracle anchor, without a role-local read.
  bool anchor = false;
};
struct RelationApplication {
  DeclarationId relation;
  std::vector<Type> arguments;
  std::vector<SpecificationSelector> operands;
  Span span;
};
struct SpecificationClause {
  enum class Kind { Target, Input, Output, Continuation } kind;
  std::string name;
  RelationApplication subject;
  std::optional<RelationApplication> residual;
  std::optional<SpecificationSelector> decision;
  Span span;
};
/// Source claim data has no security interpretation in the native frontend.
/// Argument labels are empty for positional arguments; versions are explicit
/// registry keys, never inferred from an installed native implementation.
struct ClaimExpression {
  enum class Kind { Natural, Reference, Application, Binary, Unary, List } kind;
  std::string text;
  std::optional<uint32_t> version;
  std::vector<ClaimExpression> arguments;
  std::vector<std::string> labels;
  Span span;
  /// Lexically resolved carrier for the unversioned cardinality builtin.
  /// Authored argument text remains intact; export closes this type against
  /// the selected Entry and writes its canonical nominal domain identity.
  std::optional<Type> cardinalityDomain;
};
struct SourceClaim {
  std::string label;
  ClaimExpression property;
  Span span;
};
struct SourceClaimBlock {
  std::string name, entry;
  std::vector<SourceClaim> claims;
  Span span;
  std::optional<DeclarationId> subject;
  /// Closed, checked arguments of a protocol subject; empty for proof entries.
  std::vector<Type> arguments;
};
struct SourceVerification {
  std::string block, label;
  ClaimExpression method;
  Span span;
};
struct SetupSlot {
  std::string name;
  std::vector<InputSelector> inputs;
  Span span;
};
enum class EntryKind { Run, Proof, Function };
struct RunEntry {};
/// A checked association of ordinary Local code with a protocol occurrence.
struct ConstructionRule {
  using Kind = protocol::ConstructionRuleKind;
  Kind kind;
  std::vector<std::string> path;
  DeclarationId handler;
  std::vector<Type> arguments;
  std::vector<unsigned> inputs;
  Span span;
  std::optional<Type> payload, chunks;
};
struct ConstructionMethod {
  CallableReference target;
  std::vector<Type> arguments;
};
struct ConstructionCodec {
  Type provider, record;
  ConstructionMethod initialize, write, finish;
  /// Actual shared protocol inputs used to initialize the layout record.
  std::vector<unsigned> inputs;
};
/// A child owns the complete mathematical construction at one labelled call.
/// Arguments specialize the child construction, not the protocol call inputs.
struct ConstructionApplication {
  DeclarationId construction;
  std::vector<Type> arguments;
  std::vector<std::string> path;
  Span span;
};
struct ConstructionDefinition {
  enum class Base { None, Authored, Native, Named } base = Base::None;
  enum class Root { None, Host, Local } root = Root::None;
  std::optional<DeclarationId> parent;
  std::vector<Type> arguments;
  std::optional<Type> provider;
  std::optional<Type> state;
  std::optional<CallableReference> initializer;
  std::vector<Type> initializerArguments;
  std::vector<unsigned> services;
  std::string suite;
  bool nativeBase = false;
  std::vector<ConstructionRule> rules;
  std::vector<ConstructionApplication> applications;
  std::optional<ConstructionCodec> codec;
};
/// Explicit two-participant proof job choices. Public inputs name whole logical
/// ports; acceptance can select a Boolean product component. Service indices
/// refer to managed ports, independently of native data flattening.
struct ProofEntry {
  enum class Construction {
    Authored,
    FiatShamir,
    Derived
  } construction = Construction::Authored;
  unsigned prover = 0, verifier = 0;
  std::vector<unsigned> publicInputs;
  SpecificationSelector acceptance;
  std::optional<SpecificationSelector> completion;
  std::optional<unsigned> target;
  std::vector<unsigned> services;
  std::string suite;
  std::optional<DeclarationId> selectedConstruction;
  std::vector<Type> constructionArguments;
  protocol::ProofFormat format = protocol::ProofFormat::Native;
  Span span;
};
/// A validated instance of an installed primitive scheme. The static roots are
/// inferred from the written signature, independently of parameter names/order.
struct PrimitiveDefinition {
  std::string identity;
  std::vector<Type> arguments;
};
struct Declaration {
  enum class Kind {
    Domain,
    DomainFunction,
    Math,
    Local,
    Protocol,
    Construction,
    Entry,
    EntryFunction,
    Alias,
    Record,
    Variant,
    Interface,
    Module,
    Associated,
    Relation
  } kind;
  struct Generated {
    DeclarationId target;
    std::string member;
    bool constructible = true;
    std::optional<HostInvocation::Kind> operation = {};
    /// Field order maps back to the target protocol's logical port roster.
    std::vector<InputSelector> ports = {};
    std::optional<unsigned> role = {};
    std::string identity = {};
  };
  std::optional<Generated> generated;
  DeclarationId id;
  /// Cached owning module, derived from the declaration tree; self for modules.
  DeclarationId module;
  std::string name, qualifiedName, symbol;
  bool isPublic = false;
  Span span;
  /// A domain declaration's catalog or asset term; a definition's elaborated
  /// representation.
  Type domain;
  std::vector<Parameter> parameters;
  std::vector<NaturalBound> bounds;
  std::vector<DataPrecondition> dataPreconditions;
  std::vector<PermissionBound> permissionBounds;
  std::vector<AdmissionObligation> admissions;
  std::vector<CapabilityBound> capabilityBounds;
  std::optional<Resource> resource;
  bool sealed = false;
  /// Explicit promises on associated types, independent of constructor access.
  std::optional<Permissions> permissions;
  std::vector<TypeField> fields;
  std::vector<Alternative> alternatives;
  std::vector<DeclarationId> members;
  std::optional<DeclarationId> parent;
  std::optional<Type> implementation;
  std::optional<EffectSummary> effectAllowance;
  bool abstract = false;
  std::optional<PrimitiveDefinition> primitive;
  bool completes = false;
  /// Empty or Type is a private representation; catalog sorts expose a domain.
  std::string associatedSort;
  /// A closed definition records its template and exact static substitution.
  std::optional<DeclarationId> origin;
  std::vector<Type> staticArguments;
  /// Closed helper selections, independent of runtime capture values.
  std::vector<DeclarationId> scopedArguments;
  ClosureLayout closureLayout;
  std::optional<std::pair<DeclarationId, uint32_t>> scopedOrigin;
  std::vector<std::string> roles;
  std::vector<Port> inputs, outputs;
  std::vector<ScopedParameter> scopedInputs;
  std::vector<DomainParameter> domainInputs;
  std::vector<std::shared_ptr<const DomainShape>> domainArguments;
  std::optional<Type> domainResult;
  std::shared_ptr<const DomainDefinition> domainDefinition;
  std::optional<std::string> finiteDefinition;
  std::vector<ServicePort> services;
  /// Source arguments in written order. Data, managed services and static
  /// scoped computations remain separate input categories.
  struct InputSlot {
    enum class Kind { Data, Service, Scoped, Domain } kind;
    unsigned index;
  };
  std::vector<InputSlot> inputOrder;
  std::shared_ptr<const Body> body;
  bool anonymous = false;
  std::optional<Span> specificationBlock;
  std::optional<RelationDefinition> relation;
  std::vector<SpecificationClause> specifications;
  std::vector<SourceClaimBlock> sourceClaims;
  std::vector<SourceVerification> sourceVerifications;
  std::optional<DeclarationId> target;
  std::optional<protocol::ProofFormat> proofFormat;
  std::optional<ConstructionDefinition> construction;
  std::variant<RunEntry, ProofEntry> configuration;
  /// A protocol's generated run function is selected by the protocol name.
  llvm::StringRef entryName() const {
    llvm::StringRef name = qualifiedName;
    return generated && generated->operation == HostInvocation::Kind::Run
               ? name.drop_back(5)
               : name;
  }
  EntryKind entryKind() const {
    if (kind == Kind::EntryFunction)
      return EntryKind::Function;
    return std::holds_alternative<ProofEntry>(configuration) ? EntryKind::Proof
                                                             : EntryKind::Run;
  }
  const ProofEntry *proof() const {
    return std::get_if<ProofEntry>(&configuration);
  }
  std::vector<SetupSlot> setups;
};

/// Native resolution of an authored spec's protocol owner. Terms, static
/// arguments and requests remain unelaborated until formal integration.
/// Neither owner attachment nor this record establishes any proposition.
struct PendingObligation {
  enum class Kind { Postcondition, Request } kind;
  std::optional<std::string> label;
  unsigned ordinal;
  Span span;
  std::optional<std::string> companion;
};
struct PendingSpecification {
  DeclarationId module, protocol;
  std::string name;
  bool owner = false, isPublic = false;
  Span span;
  std::vector<PendingObligation> obligations;
};

namespace detail {
struct CaptureStorage;
struct CheckedStorage;
struct ClosedStorage;
struct AnalysisStorage;
struct AuthoringStorage;
} // namespace detail
class CapturedProject;
class CheckedProject;
class Analysis;
class ClosedEntry;
struct NotationInspectionOptions;
llvm::Expected<CapturedProject> capture(std::vector<SourceBuffer>,
                                        const CaptureOptions & = {});
llvm::Expected<CapturedProject> capture(std::vector<SourceBuffer>,
                                        std::vector<AssetBuffer>,
                                        const CaptureOptions &);
Analysis analyze(const CapturedProject &, const Limits & = {},
                 source::Cancellation = {});
/// Select from checked declarations: exact qualified name, unique short name,
/// or the sole eligible Entry when the selector is empty. An explicit name is
/// resolved before checking its kind, so filtering cannot hide ambiguity.
/// Generic protocol selectors return their generated run declaration; use
/// resolveEntry to retain their checked static arguments.
llvm::Expected<DeclarationId> selectEntry(const CheckedProject &,
                                          llvm::StringRef, const Limits & = {},
                                          std::optional<EntryKind> = {});
struct EntrySelection {
  DeclarationId declaration;
  std::vector<Type> arguments;
  std::string name;
};
llvm::Expected<EntrySelection> resolveEntry(const CheckedProject &,
                                            llvm::StringRef,
                                            const Limits & = {},
                                            std::optional<EntryKind> = {});
llvm::Expected<ClosedEntry> closeEntry(const CheckedProject &, llvm::StringRef,
                                       const Limits & = {},
                                       std::optional<EntryKind> = {});
/// Close a proof declaration or a protocol specialization for semantic export.
/// An authored Host Entry function is not a protocol subject.
llvm::Expected<ClosedEntry> closeSubject(const CheckedProject &,
                                         llvm::StringRef, const Limits & = {});
/// Operation policy is used by generated child deployments; verifier ingress
/// excludes producer-only ports while retaining the checked comparison graph.
llvm::Expected<ClosedEntry> closeEntry(const CheckedProject &, llvm::StringRef,
                                       const Limits &, std::optional<EntryKind>,
                                       std::optional<HostInvocation::Kind>);

class CapturedProject {
public:
  llvm::ArrayRef<SourceBuffer> sources() const;
  llvm::ArrayRef<AssetBuffer> assets() const;
  llvm::StringRef identity() const;
  llvm::StringRef format() const;

private:
  explicit CapturedProject(std::shared_ptr<const detail::CaptureStorage>);
  std::shared_ptr<const detail::CaptureStorage> storage;
  friend llvm::Expected<CapturedProject> capture(std::vector<SourceBuffer>,
                                                 std::vector<AssetBuffer>,
                                                 const CaptureOptions &);
};

/// Check retained source places against actual capture extraction and
/// snapshots.
llvm::Error checkScopedElaboration(const CheckedProject &, const Limits & = {});
/// Relate source bodies and environments to the actual closed candidate.
llvm::Error checkScopedSpecialization(const ClosedEntry &, const Limits & = {});

/// Only successful analysis can construct this immutable owning handle.
class CheckedProject {
public:
  /// Includes installation sources; source IDs index this array.
  llvm::ArrayRef<SourceBuffer> sources() const;
  const CapturedProject &capture() const;
  llvm::ArrayRef<Asset> assets() const;
  llvm::ArrayRef<Declaration> declarations() const;
  /// Exact source occurrences with unavailable formal elaboration. An empty
  /// array means that no layout spec was requested, not verified security.
  llvm::ArrayRef<PendingSpecification> pendingSpecifications() const;
  llvm::ArrayRef<Token> tokens(SourceId) const;
  llvm::StringRef installationIdentity() const;
  uint64_t checkedWork() const;
  uint64_t checkedDeclarations() const;
  uint64_t checkedOperations() const;
  uint64_t checkedNotationDescriptors() const;
  uint64_t checkedNotationHoles() const;
  /// All named Entries (including aliases), sorted by qualified name.
  std::vector<DeclarationId> entries() const;

private:
  friend class Authoring;
  friend class Layouts;
  friend llvm::Error checkScopedElaboration(const CheckedProject &,
                                            const Limits &);
  explicit CheckedProject(std::shared_ptr<const detail::CheckedStorage>);
  std::shared_ptr<const detail::CheckedStorage> storage;
  friend Analysis analyze(const CapturedProject &, const Limits &,
                          source::Cancellation);
  friend llvm::Expected<std::string>
  inspectNotations(const CheckedProject &, const NotationInspectionOptions &,
                   const Limits &);
  friend llvm::Expected<std::string>
  inspectWrittenSource(const CheckedProject &, const Limits &);
  friend llvm::Expected<std::string>
  inspectSourceBindings(const CheckedProject &, const Limits &);
  friend llvm::Expected<std::string> inspectSourceInstances(const ClosedEntry &,
                                                            const Limits &);
  friend llvm::Expected<std::string> inspectPublicAPI(const CheckedProject &,
                                                      const Limits &);
  friend llvm::Expected<EntrySelection> resolveEntry(const CheckedProject &,
                                                     llvm::StringRef,
                                                     const Limits &,
                                                     std::optional<EntryKind>);
};

/// Recovery tokens and diagnostics cannot be promoted to checked state.
class Analysis {
public:
  /// Includes installation sources; source IDs index this array.
  llvm::ArrayRef<SourceBuffer> sources() const;
  llvm::ArrayRef<Diagnostic> diagnostics() const;
  llvm::ArrayRef<Token> tokens(SourceId) const;
  llvm::Expected<CheckedProject> checkedProject() const;

private:
  friend class Authoring;
  explicit Analysis(std::shared_ptr<const detail::AnalysisStorage>);
  std::shared_ptr<const detail::AnalysisStorage> storage;
  friend Analysis analyze(const CapturedProject &, const Limits &,
                          source::Cancellation);
};
struct ClosedInvocation;
class ClosedEntry {
public:
  const CheckedProject &project() const { return checked; }
  const Declaration &entry() const;
  /// Selected public name, including supplied static argument syntax.
  llvm::StringRef name() const;
  const Declaration &root() const;
  const Declaration *protocolOrNull() const;
  const Declaration &protocol() const;
  llvm::ArrayRef<ClosedInvocation> invocations() const;
  /// Child policy chooses executable construction dependencies downstream.
  std::optional<HostInvocation::Kind> invocationKind() const;
  /// Canonical evaluator assets required by reachable closed operations.
  /// Sorted and deduplicated by definition identity.
  llvm::ArrayRef<Asset> assets() const;
  /// Original type declarations and the selected Entry's closed instances.
  /// Only the reachable instances have bodies; declaration IDs remain local.
  llvm::ArrayRef<Declaration> declarations() const;

private:
  friend class Layouts;
  ClosedEntry(CheckedProject checked, DeclarationId selected,
              std::shared_ptr<const detail::ClosedStorage> storage)
      : checked(std::move(checked)), selected(selected),
        storage(std::move(storage)) {}
  CheckedProject checked;
  DeclarationId selected;
  std::shared_ptr<const detail::ClosedStorage> storage;
  friend llvm::Expected<ClosedEntry> closeInvocation(const CheckedProject &,
                                                     const HostInvocation &,
                                                     const Limits &);
  friend llvm::Expected<ClosedEntry>
  closeEntry(const CheckedProject &, llvm::StringRef, const Limits &,
             std::optional<EntryKind>, std::optional<HostInvocation::Kind>);
};
llvm::Expected<ClosedEntry> closeInvocation(const CheckedProject &,
                                            const HostInvocation &,
                                            const Limits & = {});
struct ClosedInvocation {
  HostInvocation::Kind kind;
  DeclarationId target;
  std::vector<Type> arguments;
  std::shared_ptr<const ClosedEntry> deployment;
};
llvm::Expected<std::string> encodeSymbol(llvm::StringRef qualifiedName,
                                         const Limits & = {});
/// Deterministic private predicate symbol for a closed relation declaration.
std::string formulaSymbol(const Declaration &);
/// Bounded native origin shared by all instances of one local declaration.
std::string logicalOrigin(const ClosedEntry &, const Declaration &);
std::string spelling(const Type &);
/// Canonical identity of the installed Contracts data, not caller-supplied
/// data.
std::string installedCatalogIdentity();
} // namespace zkc::language

#endif
