#ifndef ZKC_LANGUAGE_INTERNAL_H
#define ZKC_LANGUAGE_INTERNAL_H

#include "State.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/Support/JSON.h"
#include <map>
#include <set>

namespace zkc::language {
class Layouts;
}
namespace zkc::language::detail {
/// A label belongs to an authored argument position, not to the value's type.
struct ArgumentLabel {
  unsigned index;
  std::string name;
  Span span;
};
struct SyntaxType {
  enum class Kind {
    Hole,
    Name,
    Builtin,
    Formal,
    Natural,
    Add,
    Multiply,
    PowerOfTwo,
    Array,
    Tuple
  } kind = Kind::Name;
  std::string name;
  Span span;
  // Parser-maintained height also bounds left-associated syntax and its
  // cleanup.
  unsigned height = 1;
  std::vector<SyntaxType> arguments;
  std::vector<ArgumentLabel> labels;
};
struct NotationSyntax {
  std::shared_ptr<const NotationDescriptor> descriptor;
  Span span;
};
using NotationEnvironment = std::map<std::string, NotationSyntax>;
struct SyntaxOperator {
  std::string symbol;
  SyntaxType target;
  bool isPublic = false;
  Span span;
  std::shared_ptr<const NotationDescriptor> notation;
  bool explicitNotation = false;
  std::vector<std::string> holes;
};
struct OperatorBinding {
  std::string symbol;
  CallableReference target;
  std::vector<std::optional<Type>> arguments;
  Span span;
  std::shared_ptr<const NotationDescriptor> notation;
};
struct SyntaxSelector {
  bool output = false;
  std::string port;
  std::vector<std::string> path;
  std::optional<std::string> role;
  Span span;
};
struct SyntaxPort {
  std::string name;
  SyntaxType type;
  std::vector<std::string> roles;
  Span span;
  bool isPublic = true;
  std::optional<RelationPurpose> purpose;
  std::optional<SyntaxSelector> binding;
};
struct SyntaxParameter {
  std::string name;
  SyntaxType constraint;
  Permissions permissions;
  Span span;
};
struct SyntaxRequirement {
  std::string permission, capability;
  std::vector<SyntaxType> arguments;
  SyntaxType lhs, rhs;
  Span span;
};
struct BindingId {
  uint32_t index;
  bool operator<(BindingId other) const { return index < other.index; }
  bool operator==(BindingId other) const { return index == other.index; }
};
struct Pattern {
  enum class Kind { Name, Ignore, Unit, Tuple, Record } kind = Kind::Name;
  std::string name;
  std::optional<SyntaxType> type;
  std::vector<Pattern> children;
  std::vector<std::string> labels;
  std::optional<BindingId> binding;
  Span span;
};
struct Expression {
  enum class Kind {
    Name,
    Decimal,
    Boolean,
    Call,
    Kernel,
    Intrinsic,
    Map,
    ReductionMap,
    MethodCall,
    FinishIf,
    NotationCall,
    And,
    Or,
    Not,
    Tuple,
    Array,
    Record,
    Projection,
    If,
    Match,
    For,
    Block
  } kind;
  std::string text;
  std::vector<uint32_t> children;
  bool bracket = false;
  Span span;
  std::vector<SyntaxType> arguments;
  std::vector<ArgumentLabel> staticLabels, callLabels;
  std::vector<std::string> labels;
  /// Kernel parameter positions written as asset terms instead of literals.
  std::map<unsigned, SyntaxType> assetParameters;
  std::optional<std::vector<std::string>> roles;
  std::vector<uint32_t> regions;
  std::vector<std::vector<Pattern>> payloads;
  std::optional<BindingId> binding;
  Pattern index;
  /// For `map`, whether each argument was marked `each`.
  std::vector<bool> each;
  /// Lexical body identity, assigned before type inference.
  std::optional<uint32_t> scope;
  std::shared_ptr<const NotationDescriptor> notation;
  unsigned height = 1;
  bool grouped = false;
  bool reductionCall = false;
  uint32_t reducerExpression = 0, reductionOrdinal = 0;
};
struct Statement {
  enum class Kind {
    Let,
    Assign,
    Expression,
    Drop,
    Consume,
    Require
  } kind = Kind::Let;
  Pattern pattern;
  bool mutableBinding = false;
  bool terminated = true;
  std::optional<SyntaxType> type;
  std::optional<std::vector<std::string>> roles;
  std::optional<std::pair<std::string, std::string>> exchange;
  std::optional<std::string> owner;
  uint32_t expression;
  Span span;
};
struct SyntaxBody {
  std::vector<SyntaxOperator> operators;
  std::vector<OperatorBinding> resolvedOperators;
  std::optional<uint32_t> parent;
  std::shared_ptr<const NotationEnvironment> notationEnvironment;
  std::vector<Statement> statements;
  std::vector<std::pair<std::string, uint32_t>> results;
  bool stopped = false;
  bool returned = false;
  bool region = false;
  std::string stopReason;
  Span span;
};
struct SyntaxAlternative {
  std::string name;
  std::vector<SyntaxPort> fields;
  Span span;
};
struct SyntaxSubject {
  std::optional<unsigned> inlineMember;
  SyntaxType relation;
  std::vector<SyntaxSelector> operands;
  Span span;
};
struct SyntaxClause {
  SpecificationClause::Kind kind;
  std::string name;
  SyntaxSubject subject;
  std::optional<SyntaxSubject> residual;
  std::optional<SyntaxSelector> decision;
  Span span;
};
struct SyntaxRelation {
  RelationDefinition::Kind kind = RelationDefinition::Kind::Formula;
  std::string externalKind, key, revision, asset;
};
struct SyntaxName {
  std::string name;
  Span span;
};
struct SyntaxSetupSlot {
  SyntaxName name;
  std::vector<SyntaxSelector> inputs;
  Span span;
};
struct SyntaxProofEntry {
  SyntaxName prover, verifier;
  std::vector<SyntaxName> publicInputs;
  SyntaxSelector acceptance;
  std::optional<SyntaxSelector> completion;
  std::optional<SyntaxName> target, service;
  ProofEntry::Construction construction = ProofEntry::Construction::Authored;
  std::string suite;
  Span span;
};
struct Binding {
  std::string name;
  Span span;
  bool mutableBinding = false;
  bool service = false;
  unsigned scope = 0;
};
/// Token intervals refer to the module's non-trivia token sequence. Fixed
/// declaration headers are collected before imports; expression bodies are
/// parsed only after their module environment is known.
struct DeferredBody {
  size_t begin, end;
  unsigned depth;
  bool protocol;
};
struct SyntaxDeclaration {
  Declaration::Kind kind;
  /// A domain declaration's target is its sort word; its domain is the
  /// installed identity or, for an asset domain, the captured asset name.
  std::string name, domain, target;
  bool assetDomain = false;
  std::optional<std::string> primitive;
  bool isPublic = false;
  bool completes = false;
  Span span;
  std::vector<std::string> roles;
  std::vector<SyntaxPort> inputs, outputs, services;
  std::vector<Declaration::InputSlot> inputOrder;
  std::vector<Expression> expressions;
  std::optional<DeferredBody> deferredBody;
  // Root body is kept in the first slot; nested bodies use stable indices.
  std::vector<SyntaxBody> bodies;
  // Resolved lexical identities are private elaboration data, never serialized.
  std::vector<Binding> bindings;
  std::vector<BindingId> inputBindings, serviceBindings;
  bool resolved = false;
  bool elaborated = false;
  std::vector<SyntaxParameter> parameters;
  std::vector<SyntaxRequirement> requirements;
  bool explicitRequirements = false;
  std::optional<Permissions> permissions;
  std::optional<Effects> effects;
  std::optional<SyntaxType> definition;
  std::vector<SyntaxType> targetArguments;
  std::vector<ArgumentLabel> targetLabels;
  std::vector<SyntaxPort> fields;
  std::vector<SyntaxAlternative> alternatives;
  std::vector<SyntaxDeclaration> members;
  bool abstract = false;
  std::string associatedSort;
  std::optional<SyntaxRelation> relation;
  bool anonymous = false;
  std::optional<Span> specificationBlock;
  std::vector<SyntaxClause> specifications;
  std::optional<SyntaxProofEntry> proof;
  std::vector<SyntaxSetupSlot> setups;
  bool entryBlock = false;
  EntryKind entryKind = EntryKind::Run;
};
struct Import {
  std::string module;
  std::vector<std::string> names;
  Span span;
  std::optional<std::string> alias;
  std::vector<std::string> operators, notations, reductions;
  bool isPublic = false;
};
std::string operatorBindingKey(const OperatorBinding &,
                               llvm::ArrayRef<Declaration>);
llvm::StringRef operatorSymbol(const Expression &);
struct SyntaxModule {
  ModuleId id;
  std::vector<Import> imports;
  std::vector<SyntaxDeclaration> declarations;
  std::vector<SyntaxOperator> operators;
};
llvm::Error lex(const SourceBuffer &, ModuleId, Work &, std::vector<Token> &);
llvm::Expected<SyntaxModule> parse(const SourceBuffer &, ModuleId,
                                   llvm::ArrayRef<Token>, Work &);
llvm::Error parseBodies(const SourceBuffer &, SyntaxModule &,
                        llvm::ArrayRef<Token>,
                        std::shared_ptr<const NotationEnvironment>, Work &);
NotationEnvironment fixedNotationEnvironment(ModuleId);
llvm::Error resolveNotationSyntax(std::vector<SyntaxOperator> &,
                                  NotationEnvironment &, Work &);
llvm::Error check(std::vector<SyntaxModule>, CheckedStorage &, Work &);
llvm::Error checkSetups(const ClosedEntry &, Layouts &, Work &);
llvm::Error checkCapabilityInstallation();
} // namespace zkc::language::detail

#endif
