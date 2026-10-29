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
struct EntrySelector {
  SyntaxType target;
  /// Whitespace/comments removed, with string tokens preserved verbatim.
  std::string arguments;
};
llvm::Expected<EntrySelector> parseEntrySelector(llvm::StringRef, Work &);
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
  std::optional<SyntaxType> filtered;
};
struct BoundNotationTarget {
  CallableReference target;
  std::vector<std::optional<Type>> arguments;
};
struct OperatorBinding {
  std::string symbol;
  CallableReference target;
  std::vector<std::optional<Type>> arguments;
  Span span;
  std::shared_ptr<const NotationDescriptor> notation;
  std::optional<BoundNotationTarget> filtered = {};
};
using NotationFamilies = std::map<uint32_t, std::vector<OperatorBinding>>;
struct SyntaxSelector {
  bool output = false;
  std::string port;
  std::vector<std::string> path;
  std::optional<std::string> role;
  Span span;
};
struct SyntaxItemOrigin {
  std::string input, domain;
  Span span;
};
struct SyntaxScopedSignature {
  ScopedSignature::Mode mode;
  std::vector<SyntaxType> inputs;
  SyntaxType result;
  Effects allowance;
  bool explicitAllowance = false;
  std::vector<std::string> inputLabels;
  std::vector<SyntaxItemOrigin> itemOrigins;
};
struct SyntaxPort {
  std::string name;
  SyntaxType type;
  std::vector<std::string> roles;
  Span span;
  bool isPublic = true;
  std::optional<RelationPurpose> purpose;
  std::optional<SyntaxSelector> binding;
  std::optional<SyntaxScopedSignature> scoped;
  std::optional<SyntaxType> domain;
  bool unnamed = false;
  /// Installed declaration selected by name resolution, never by the parser.
  std::optional<std::string> serviceConstructor;
};
struct SyntaxParameter {
  std::string name;
  SyntaxType constraint;
  Permissions permissions;
  std::vector<std::string> writtenPermissions;
  Span span;
};
struct SyntaxInputSelector {
  std::string port;
  std::vector<std::string> path;
  Span span;
};
struct SyntaxRequirement {
  std::optional<DataPrecondition::Kind> data;
  SyntaxInputSelector left, right;
  unsigned leftAxis = 0, rightAxis = 0;
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
  std::vector<bool> shorthand;
  std::optional<BindingId> binding;
  /// Original binder token in its source module, retained across parser sugar.
  /// It is private provenance, never an exported identity.
  std::optional<uint32_t> writtenToken;
  Span span;
};
struct Expression {
  enum class Kind {
    Name,
    Lambda,
    Decimal,
    Boolean,
    Call,
    Kernel,
    Intrinsic,
    Map,
    DomainProduct,
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
    Subscript,
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
  // Authored constructor occurrences for nominal match resolution/navigation.
  std::vector<Span> constructorSpans;
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
  /// Written finite binders, before parser expansion into product/lambda nodes.
  std::vector<std::pair<Pattern, uint32_t>> reductionBinders;
  std::optional<uint32_t> reductionPredicate, reductionBody;
  unsigned height = 1;
  bool grouped = false;
  bool shorthand = false;
  bool filteredReduction = false;
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
  std::optional<std::string> site;
  uint32_t expression;
  Span span;
  enum class Evaluation {
    Legacy,
    Pure,
    Ordered
  } evaluation = Evaluation::Legacy;
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
  /// Mathematical final expression; checking still requires a complete result.
  bool implicitResult = false;
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
  std::optional<SyntaxType> selectedConstruction;
  Span span;
};
struct Binding {
  std::string name;
  Span span;
  bool mutableBinding = false;
  bool service = false;
  bool scoped = false;
  unsigned scope = 0;
  bool domain = false;
  std::optional<LexicalNode> written = {};
};
/// Token intervals refer to the module's non-trivia token sequence. Fixed
/// declaration headers are collected before imports; expression bodies are
/// parsed only after their module environment is known.
struct DeferredBody {
  size_t begin, end;
  unsigned depth;
  bool protocol;
};
struct SyntaxConstructionRule {
  ConstructionRule::Kind kind;
  std::vector<SyntaxName> path;
  unsigned member;
  std::vector<SyntaxName> parameters;
  Span span;
};
struct SyntaxConstructionApplication {
  SyntaxType construction;
  std::vector<SyntaxName> path;
  Span span;
};
struct SyntaxConstruction {
  ConstructionDefinition::Base base = ConstructionDefinition::Base::None;
  std::optional<SyntaxType> parent, provider;
  std::optional<SyntaxType> codec;
  std::vector<SyntaxName> layout;
  std::vector<SyntaxName> services;
  std::string suite;
  std::vector<SyntaxConstructionRule> rules;
  std::vector<SyntaxConstructionApplication> applications;
};
struct Import {
  std::string module;
  std::optional<DeclarationId> target;
  std::optional<DeclarationId> provider;
  std::vector<std::string> names;
  Span span;
  std::optional<std::string> alias;
  bool explicitAlias = false;
  std::vector<std::string> operators, notations, reductions;
  bool isPublic = false, indexing = false;
};
struct SyntaxSourceClaimBlock {
  SourceClaimBlock value;
  SyntaxType subject;
};
struct FormalSource;
/// Header attachment and frozen authored formal facts. The parser snapshot is
/// used only while completing bodies; consumers use the grammar-neutral model.
struct FormalSyntax {
  syntax::Snapshot tree;
  syntax::NodeId node;
  std::optional<SyntaxType> subject;
  std::string name;
  bool isPublic = false;
  std::shared_ptr<const FormalSource> authored;
};
struct SyntaxDeclaration {
  std::vector<FormalSyntax> formalSyntax;
  /// Private link to the frozen authored header, assigned before expansion.
  /// Not serialized and never an artifact or proof identity.
  std::optional<uint32_t> writtenDeclaration;
  bool layoutSyntax = false;
  bool invalidBody = false;
  /// Authored parameter group, erased before native declaration collection.
  bool section = false;
  std::optional<std::string> generated;
  Declaration::Kind kind;
  /// A domain declaration's target is its sort word; its domain is the
  /// installed identity or, for an asset domain, the captured asset name.
  std::string name, domain, target;
  bool assetDomain = false;
  std::optional<std::string> primitive;
  std::optional<std::string> domainConstructor, finiteDefinition;
  std::optional<SyntaxType> domainResult;
  bool isPublic = false;
  bool explicitPublic = false;
  bool completes = false;
  Span span;
  std::vector<std::string> roles;
  std::vector<SyntaxPort> inputs, outputs, services, scopedInputs, domainInputs;
  std::vector<Declaration::InputSlot> inputOrder;
  std::vector<Expression> expressions;
  std::optional<DeferredBody> deferredBody;
  // Root body is kept in the first slot; nested bodies use stable indices.
  std::vector<SyntaxBody> bodies;
  // Resolved lexical identities are private elaboration data, never serialized.
  std::vector<Binding> bindings;
  std::vector<BindingId> inputBindings, serviceBindings, scopedBindings,
      domainBindings;
  bool resolved = false;
  bool elaborated = false;
  std::vector<SyntaxParameter> parameters;
  std::vector<SyntaxRequirement> requirements;
  bool explicitRequirements = false;
  std::optional<Permissions> permissions;
  std::vector<std::string> writtenPermissions;
  std::optional<Resource> resource;
  bool sealed = false;
  std::optional<Effects> effects;
  std::vector<std::string> effectDependencies;
  std::optional<SyntaxType> definition;
  std::vector<SyntaxType> targetArguments;
  std::vector<ArgumentLabel> targetLabels;
  std::vector<SyntaxPort> fields;
  std::vector<SyntaxAlternative> alternatives;
  std::vector<SyntaxDeclaration> members;
  std::vector<Import> imports;
  std::vector<SyntaxOperator> operators;
  bool externalModule = false;
  bool abstract = false;
  std::string associatedSort;
  std::optional<SyntaxRelation> relation;
  bool anonymous = false;
  std::optional<Span> specificationBlock;
  std::vector<SyntaxClause> specifications;
  std::vector<SyntaxSourceClaimBlock> sourceClaims;
  std::vector<SourceVerification> sourceVerifications;
  std::optional<SyntaxProofEntry> proof;
  std::optional<protocol::ProofFormat> proofFormat;
  std::optional<SyntaxConstruction> construction;
  bool constructionHandler = false;
  std::vector<SyntaxSetupSlot> setups;
  bool entryBlock = false;
  EntryKind entryKind = EntryKind::Run;
};
/// Static source arrays project a literal element. Receiver typing belongs to
/// each caller; this predicate only reads retained authored syntax.
inline std::optional<llvm::StringRef>
staticSubscriptIndex(const SyntaxDeclaration &syntax, const Expression &expr) {
  if (expr.kind != Expression::Kind::Subscript || expr.children.size() != 2)
    return {};
  const auto &index = syntax.expressions.at(expr.children[1]);
  if (index.kind != Expression::Kind::Decimal)
    return {};
  return index.text;
}

std::string operatorBindingKey(const OperatorBinding &,
                               llvm::ArrayRef<Declaration>);
llvm::StringRef operatorSymbol(const Expression &);

llvm::Error lex(const SourceBuffer &, SourceId, Work &, std::vector<Token> &);
llvm::Expected<SyntaxDeclaration> parse(const SourceBuffer &, SourceId,
                                        llvm::ArrayRef<Token>, Work &);
struct BodyParseScope {
  SyntaxDeclaration *module;
  std::shared_ptr<const NotationEnvironment> environment;
};
llvm::Error parseBodies(const SourceBuffer &, SourceId, llvm::ArrayRef<Token>,
                        llvm::ArrayRef<BodyParseScope>, Work &);
llvm::Expected<SyntaxDeclaration>
parseLayoutHeaders(const SourceBuffer &, SourceId, CheckedStorage &, Work &);
llvm::Error parseLayoutBodies(SourceId, llvm::ArrayRef<BodyParseScope>,
                              CheckedStorage &, Work &,
                              std::vector<Diagnostic> *recovery = nullptr);
llvm::Error expandLayoutSections(std::vector<SyntaxDeclaration> &, Work &);
NotationEnvironment fixedNotationEnvironment(SourceId);
llvm::Error resolveNotationSyntax(std::vector<SyntaxOperator> &,
                                  NotationEnvironment &, Work &);
llvm::Error check(std::vector<SyntaxDeclaration>, CheckedStorage &, Work &,
                  AnalysisStorage * = nullptr);
llvm::Error checkSetups(const ClosedEntry &, Layouts &, Work &);
llvm::Error checkClosedSourceClaims(const ClosedEntry &, Work &);
llvm::Error checkCapabilityInstallation();
} // namespace zkc::language::detail

#endif
