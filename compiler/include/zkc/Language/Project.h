#ifndef ZKC_LANGUAGE_PROJECT_H
#define ZKC_LANGUAGE_PROJECT_H

#include "zkc/Contracts/Mathematical.h"
#include "zkc/Language/Assets.h"
#include "zkc/Language/Types.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <variant>
#include <vector>

namespace zkc::language {
struct ModuleId {
  uint32_t index;
};
struct DeclarationId {
  uint32_t index;
};
struct ValueId {
  uint32_t index;
};
struct ServiceId {
  uint32_t index;
};
struct Span {
  ModuleId module;
  uint32_t begin, end;
};
struct Diagnostic {
  std::string code, message;
  std::optional<Span> primary;
  std::vector<Span> related;
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
  uint64_t declarations = 10000, operations = 100000, work = 4000000;
  uint64_t irBytes = 16777216, symbolBytes = 4096;
  uint64_t interfaceBytes = 4194304, locationBytes = 16777216;
  uint64_t typeDepth = 32, typeNodes = 100000, instances = 4096;
  uint64_t aggregateLeaves = 1024, naturalTerms = 1024, naturalFactors = 64;
};
llvm::Error checkLimits(const Limits &);

/// Names and bytes determine identity. diagnosticPath is never opened here.
struct SourceBuffer {
  std::string module, text, diagnosticPath;
};
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
struct Port {
  std::string name;
  Type type;
  std::vector<unsigned> roles;
  Span span;
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
struct HelperCall {
  DeclarationId callee;
  std::vector<ValueId> operands;
  std::vector<Type> arguments;
  std::optional<Type> component;
  std::optional<unsigned> owner;
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
struct ServiceQuery {
  ServiceId service;
  /// The static UniformIndex domain size of an `index` query; absent for
  /// `draw`. Closed values are powers of two no greater than 2^63.
  std::optional<Natural> bound;
};
struct Require {
  ValueId condition;
  /// Absent in a local function, whose caller supplies its execution owner.
  std::optional<unsigned> owner;
};
struct ProtocolCompletion {
  ValueId condition;
  unsigned owner;
  /// Owner output order; continuations index the logical values moved on false.
  std::vector<ValueId> values;
  std::vector<unsigned> continuations;
};
struct Exchange {
  unsigned sender, receiver;
  ValueId payload;
};
struct Restriction {
  ValueId input;
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
};
struct Operation {
  std::variant<MathValue, HelperCall, BulkApplication, Exchange, Restriction,
               Construct, Projection, LocalPrimitive, Consume, LocalControl,
               ProtocolApplication, ServiceQuery, Require, ProtocolRepeat,
               ProtocolCompletion>
      action;
  /// Each result has its own type and participant availability.
  std::vector<ValueId> results;
  Span span;
  uint32_t statement;
};
struct Body {
  enum class Mode { Math, Local, Protocol } mode;
  std::vector<ServicePort> services;
  std::vector<Value> values;
  std::vector<Operation> operations;
  std::vector<ValueId> results;
  unsigned inputs = 0;
  bool stopped = false;
  std::string stopReason;
  bool mayStop = false, opaque = false;
  /// Includes intermediate dependencies of unused mathematical work.
  std::vector<std::vector<unsigned>> formationRequirements;
};
struct Parameter {
  enum class Sort { Type, Natural, Component, Domain, Asset } sort;
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
struct NaturalBound {
  Natural lhs, rhs;
  Span span;
  bool inferred = false;
};
struct PermissionBound {
  Type type;
  Permissions permissions;
  Span span;
};
/// A catalog proposition, independent of runtime custody permissions.
struct CapabilityBound {
  std::string predicate;
  std::vector<Type> arguments;
  Span span;
  bool inferred = false;
};
/// Upper bounds on the observable effects of a callable.
struct Effects {
  bool mayStop = false;
  bool opaque = false;
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
/// A logical input subtree, shared by every participant component of the port.
struct EntryInput {
  unsigned port = 0;
  std::vector<unsigned> path;
  Span span;
};
struct SetupSlot {
  std::string name;
  std::vector<EntryInput> inputs;
  Span span;
};
enum class EntryKind { Run, Proof };
struct RunEntry {};
/// Explicit two-participant proof job choices. Public inputs name whole logical
/// ports; acceptance can select a Boolean product component. Service indices
/// refer to managed ports, independently of native data flattening.
struct ProofEntry {
  enum class Construction {
    Authored,
    FiatShamir
  } construction = Construction::Authored;
  unsigned prover = 0, verifier = 0;
  std::vector<unsigned> publicInputs;
  SpecificationSelector acceptance;
  std::optional<SpecificationSelector> completion;
  std::optional<unsigned> target, service;
  std::string suite;
  Span span;
};
struct Declaration {
  enum class Kind {
    Domain,
    Math,
    Local,
    Protocol,
    Entry,
    Alias,
    Record,
    Variant,
    Interface,
    Component,
    Associated,
    Relation
  } kind;
  DeclarationId id;
  ModuleId module;
  std::string name, qualifiedName, symbol;
  bool isPublic = false;
  Span span;
  /// A domain declaration's catalog or asset term; a definition's elaborated
  /// representation.
  Type domain;
  std::vector<Parameter> parameters;
  std::vector<NaturalBound> bounds;
  std::vector<PermissionBound> permissionBounds;
  std::vector<CapabilityBound> capabilityBounds;
  std::optional<Permissions> permissions;
  std::vector<TypeField> fields;
  std::vector<Alternative> alternatives;
  std::vector<DeclarationId> members;
  std::optional<DeclarationId> parent;
  std::optional<Type> implementation;
  std::optional<Effects> effectAllowance;
  bool abstract = false;
  bool completes = false;
  /// Empty or Type is a private representation; catalog sorts expose a domain.
  std::string associatedSort;
  /// A closed definition records its template and exact static substitution.
  std::optional<DeclarationId> origin;
  std::vector<Type> staticArguments;
  std::vector<std::string> roles;
  std::vector<Port> inputs, outputs;
  std::vector<ServicePort> services;
  /// Protocol source arguments in written order. Data and managed identities
  /// remain separate in the checked body and native signatures.
  struct InputSlot {
    enum class Kind { Data, Service } kind;
    unsigned index;
  };
  std::vector<InputSlot> inputOrder;
  std::shared_ptr<const Body> body;
  bool anonymous = false;
  std::optional<Span> specificationBlock;
  std::optional<RelationDefinition> relation;
  std::vector<SpecificationClause> specifications;
  std::optional<DeclarationId> target;
  std::variant<RunEntry, ProofEntry> configuration;
  EntryKind entryKind() const {
    return std::holds_alternative<ProofEntry>(configuration) ? EntryKind::Proof
                                                             : EntryKind::Run;
  }
  const ProofEntry *proof() const {
    return std::get_if<ProofEntry>(&configuration);
  }
  std::vector<SetupSlot> setups;
};

namespace detail {
struct CaptureStorage;
struct CheckedStorage;
struct ClosedStorage;
struct AnalysisStorage;
} // namespace detail
class CapturedProject;
class CheckedProject;
class Analysis;
class ClosedEntry;
llvm::Expected<CapturedProject> capture(std::vector<SourceBuffer>,
                                        const CaptureOptions & = {});
llvm::Expected<CapturedProject> capture(std::vector<SourceBuffer>,
                                        std::vector<AssetBuffer>,
                                        const CaptureOptions &);
Analysis analyze(const CapturedProject &, const Limits & = {});
/// Select from checked declarations: exact qualified name, unique short name,
/// or the sole eligible Entry when the selector is empty. An explicit name is
/// resolved before checking its kind, so filtering cannot hide ambiguity.
llvm::Expected<DeclarationId> selectEntry(const CheckedProject &,
                                          llvm::StringRef, const Limits & = {},
                                          std::optional<EntryKind> = {});
llvm::Expected<ClosedEntry> closeEntry(const CheckedProject &, llvm::StringRef,
                                       const Limits & = {},
                                       std::optional<EntryKind> = {});

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

/// Only successful analysis can construct this immutable owning handle.
class CheckedProject {
public:
  const CapturedProject &capture() const;
  llvm::ArrayRef<Asset> assets() const;
  llvm::ArrayRef<Declaration> declarations() const;
  llvm::ArrayRef<Token> tokens(ModuleId) const;
  llvm::StringRef installationIdentity() const;
  uint64_t checkedWork() const;
  /// All named Entries (including aliases), sorted by qualified name.
  std::vector<DeclarationId> entries() const;

private:
  friend class Layouts;
  explicit CheckedProject(std::shared_ptr<const detail::CheckedStorage>);
  std::shared_ptr<const detail::CheckedStorage> storage;
  friend Analysis analyze(const CapturedProject &, const Limits &);
};

/// Recovery tokens and diagnostics cannot be promoted to checked state.
class Analysis {
public:
  llvm::ArrayRef<Diagnostic> diagnostics() const;
  llvm::ArrayRef<Token> tokens(ModuleId) const;
  llvm::Expected<CheckedProject> checkedProject() const;

private:
  explicit Analysis(std::shared_ptr<const detail::AnalysisStorage>);
  std::shared_ptr<const detail::AnalysisStorage> storage;
  friend Analysis analyze(const CapturedProject &, const Limits &);
};
class ClosedEntry {
public:
  const CheckedProject &project() const { return checked; }
  const Declaration &entry() const;
  const Declaration &protocol() const;
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
  friend llvm::Expected<ClosedEntry> closeEntry(const CheckedProject &,
                                                llvm::StringRef, const Limits &,
                                                std::optional<EntryKind>);
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
