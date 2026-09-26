#ifndef ZKC_FRONTEND_LIBRARY_H
#define ZKC_FRONTEND_LIBRARY_H

#include "zkc/Frontend/Work.h"

#include "zkc/Contracts/Generic.h"
#include "zkc/Frontend/Module.h"
#include <map>
#include <set>
#include <variant>

namespace zkc::frontend::library {

// All builders are untrusted inputs. Only the immutable handles below
// denote successful judgments. Exact framed content, not a digest, decides
// equality; fingerprints are SHA-256 cache locators only.
struct LibraryId {
  std::string nameSpace, name, version, resolution;
};
struct QualifiedDecl {
  LibraryId library;
  std::vector<std::string> module;
  std::string name;
};
struct Sort {
  enum class Kind { Type, Domain, Natural, Association, Component };
  Kind kind = Kind::Type;
  std::string domain; // Required only for Domain, e.g. "field".
  static Sort type();
  static Sort domainOf(std::string);
  static Sort natural();
  static Sort association();
  static Sort component();
};
struct StaticTerm {
  enum class Kind { Root, Project, Apply, Natural, Seal };
  Kind kind = Kind::Root;
  QualifiedDecl declaration;
  std::vector<StaticTerm> arguments;
  std::string member;
  uint64_t number = 0;
  static StaticTerm root(QualifiedDecl);
  static StaticTerm project(StaticTerm, std::string);
  static StaticTerm apply(QualifiedDecl, std::vector<StaticTerm>);
  static StaticTerm natural(uint64_t);
  static StaticTerm seal(QualifiedDecl, StaticTerm enclosing);
};
struct Permissions {
  bool copy = false, drop = true;
};
struct StaticDeclaration {
  QualifiedDecl id;
  Sort result;
  std::vector<Sort> parameters;
  std::map<std::string, Sort> members;
  // Captured exact descriptor bytes and ordered hidden actuals enter identity.
  // Never use a bare digest here as evidence of descriptor equality.
  std::string capturedSubject;
  std::vector<StaticTerm> capturedDependencies = {};
  bool parameter = false;
  bool seal = false;
};
struct Type {
  enum class Kind {
    Logical,
    Parameter,
    Abstract,
    Product,
    Record,
    Array,
    Variant
  };
  Kind kind = Kind::Product;
  std::string name;          // Logical constructor or abstract member.
  QualifiedDecl declaration; // Nominal record / type parameter identity.
  std::vector<StaticTerm> arguments;
  std::vector<Type> elements;
  std::vector<std::string>
      fields; // Record fields or variant alternatives, ordered with elements.
  static Type logical(std::string, std::vector<StaticTerm> = {});
  static Type parameter(QualifiedDecl);
  static Type abstract(StaticTerm, std::string);
  static Type product(std::vector<Type>);
  static Type record(QualifiedDecl, std::vector<std::string>,
                     std::vector<Type>);
  static Type array(Type, StaticTerm count);
  // Finite nominal alternatives; only the selected payload is stored.
  static Type variant(QualifiedDecl, std::vector<std::string>,
                      std::vector<Type>);
};
struct Requirement {
  // Empty relation is equality (exactly two same-sort arguments).
  std::string relation;
  std::vector<StaticTerm> arguments;
};
struct TypeBound {
  QualifiedDecl parameter;
  Permissions permissions;
};
struct Port {
  Type type;
  std::string role; // Empty means role-free; no implicit role transfer.
};
struct Signature {
  std::vector<Port> inputs, outputs;
  std::vector<Requirement> preconditions, postconditions;
  std::set<std::string> effects;
  // Empty means positional-only; otherwise one unique public label per input.
  std::vector<std::string> inputLabels = {};
};
struct TypeMember {
  std::string name;
  Permissions permissions;
};
struct StaticMember {
  std::string name;
  Sort sort;
  std::optional<StaticTerm> equation;
};
struct Facet {
  std::string owner, name;
  bool required = true;
};
struct InterfaceDecl {
  QualifiedDecl id;
  StaticTerm self;
  std::vector<TypeMember> types;
  std::vector<StaticMember> statics;
  std::map<std::string, Signature> functions;
  std::vector<TypeBound> typeBounds;
  std::vector<Requirement> requirements;
  std::vector<Facet> facets;
};
struct LogicalType {
  generic::TypeConstructor contract;
  // Installed type contracts own these permissions. Source declarations do not.
  bool droppable = true;
};
struct LogicalOperation {
  generic::Operation contract;
  std::set<std::string> effects;
};
struct CapturedLibrary {
  LibraryId id;
  std::vector<QualifiedDecl> declarations;
};
struct Environment {
  std::vector<CapturedLibrary> libraries;
  std::vector<StaticDeclaration> statics;
  std::vector<LogicalType> logicalTypes;
  std::vector<LogicalOperation> operations;
  std::vector<requirements::Implication> implications;
  uint64_t expansionLimit = 4096;
};
class Interface {
  struct Data;
  std::shared_ptr<const Data> data;
  explicit Interface(std::shared_ptr<const Data>);
  friend llvm::Expected<Interface> formInterface(InterfaceDecl, Environment);

public:
  const InterfaceDecl &declaration() const;
  const Environment &environment() const;
  const std::string &identity() const;
  const std::string &fingerprint() const;
};
struct Import {
  StaticTerm parameter;
  Interface interface;
};
struct Substitution {
  std::vector<std::pair<StaticTerm, StaticTerm>> statics;
  std::vector<std::pair<QualifiedDecl, Type>> types;
};
// A formed public function contract, independent of its implementation body.
struct CallableDecl {
  QualifiedDecl id;
  Signature signature;
  std::vector<QualifiedDecl> parameters;
  std::vector<TypeBound> typeBounds;
  std::vector<Import> imports;
};
class Callable {
  struct Data;
  std::shared_ptr<const Data> data;
  explicit Callable(std::shared_ptr<const Data>);
  friend llvm::Expected<Callable> formCallable(CallableDecl, Environment);

public:
  const CallableDecl &declaration() const;
  const Environment &environment() const;
  const std::string &identity() const;
};
llvm::Expected<Callable> formCallable(CallableDecl, Environment);
struct SourceCall {
  Callable callable;
  // Includes component actuals, checked against exact imported interfaces.
  Substitution arguments;
};
struct Value {
  ValueId id;
  Port port;
};
struct Place {
  ValueId value;
  std::vector<unsigned> path; // Semantic field / fixed index, never leaf names.
};
struct MemberCall {
  StaticTerm component;
  std::string member;
};
struct LogicalCall {
  std::string operation;
  std::vector<StaticTerm> arguments;
};
struct Call {
  std::variant<MemberCall, LogicalCall, SourceCall> target;
  std::string role;
  std::vector<Place> inputs;
  std::vector<Value> outputs;
  std::vector<std::string> attributes;
};
struct Construct {
  Value output;
  std::vector<Place> elements;
};
struct Project {
  Place input;
  Value output;
};
struct Drop {
  Place input;
};
struct Region;
struct VariantConstruct {
  Value output;
  std::string alternative;
  Place payload;
};
struct MatchArm {
  std::string alternative;
  std::shared_ptr<const Region> body;
};
// Shared storage for exhaustive local branches; the Instruction alternative
// determines whether input is a variant scrutinee or a Boolean condition.
struct LocalBranches {
  Place input;
  std::string role;
  std::vector<Place> captures;
  std::vector<Value> outputs;
  std::vector<MatchArm> arms;
};
using Match = LocalBranches;
// Boolean selection with exactly the "then" and "else" arms. Unlike Match,
// inputs of each isolated arm are captures only (there is no payload).
struct Conditional {
  LocalBranches branches;
};
struct ArrayTraversal {
  Place input;
  std::string role;
  std::vector<Place> initial, captures;
  std::vector<Value> outputs;
  std::shared_ptr<const Region> body;
  // When present, the region returns one element after its carried state.
  // The result collects those elements in traversal order, including N=0.
  std::optional<Value> collected = std::nullopt;
};
// Terminal, uncatchable failure of the whole computation. No continuation ever
// observes a stopped region: nothing may follow it, it produces no result, and
// no caller, arm join or traversal turns it back into a value. It is not an
// error value and has no recovery form.
struct Stop {
  // The terminal reason of the common source model, unchanged: one of
  // "reject", "abort", "exhausted", "incomplete", "refused". A checked library
  // body is a role-free local algorithm, so a stop here ends that whole
  // algorithm and names no participant.
  std::string reason;
};
using Instruction =
    std::variant<Call, Construct, Project, Drop, VariantConstruct, Match,
                 ArrayTraversal, Stop, Conditional>;
// Shared traversal of the two checked local branch forms.
const LocalBranches *branches(const Instruction &);
LocalBranches *branches(Instruction &);
// Isolated scope. Conditional inputs: captures. Match inputs: payload,
// captures. Traversal inputs: element, carried states, captures. ValueIds are
// unique throughout the containing body. A region that cannot continue — see
// terminal() — returns nothing and owes no result, yield, postcondition or
// remaining-resource obligation.
struct Region {
  std::vector<Value> inputs;
  std::vector<Instruction> instructions;
  std::vector<Place> returns;
};
struct Body {
  QualifiedDecl id;
  Signature signature;
  std::vector<TypeBound> typeBounds;
  std::vector<Value> inputs;
  std::vector<Instruction> instructions;
  std::vector<Place> returns;
};
class CheckedBody {
  struct Data;
  std::shared_ptr<const Data> data;
  explicit CheckedBody(std::shared_ptr<const Data>);
  friend llvm::Expected<CheckedBody> checkBody(Body, Environment,
                                               std::vector<Import>);

public:
  const Body &body() const;
  const Environment &environment() const;
  const std::vector<Import> &imports() const;
  const std::vector<Requirement> &obligations() const;
  const std::string &identity() const;
  const std::string &fingerprint() const;
};

// Members have concrete typed bodies. A conforming implementation may expose
// fewer effects/preconditions and stronger postconditions, but never invented
// postconditions: checked bodies must derive them from checked operations.
// Persistent template obligations do not depend on member use or selection.
struct ComponentDecl {
  Interface interface;
  std::map<std::string, Type> representations;
  std::map<std::string, StaticTerm> statics;
  std::map<std::string, CheckedBody> functions;
  std::vector<Import> imports = {};
  std::vector<TypeBound> typeBounds = {};
  std::vector<Requirement> requirements = {};
};
class CheckedComponent {
  struct Data;
  std::shared_ptr<const Data> data;
  explicit CheckedComponent(std::shared_ptr<const Data>);
  friend llvm::Expected<CheckedComponent> checkComponent(ComponentDecl,
                                                         Environment);

public:
  const ComponentDecl &declaration() const;
  const Environment &environment() const;
  const std::string &identity() const;
  const std::string &fingerprint() const;
};
struct Implementation;
struct Binding {
  StaticTerm parameter;
  std::shared_ptr<const Implementation> implementation;
  std::string importPath;
};
struct Implementation {
  StaticTerm selection;
  Interface interface;
  std::map<std::string, Type> representations;
  std::map<std::string, StaticTerm> statics;
  std::map<std::string, CheckedBody> functions;
  std::vector<Binding> dependencies;
  Substitution arguments;
  std::vector<Import> imports = {};
  std::vector<TypeBound> typeBounds = {};
  std::vector<Requirement> requirements = {};
  std::optional<Environment> environment = std::nullopt;
};
struct LayoutLeaf {
  enum class Kind { Logical, ResourceUnit, Variant };
  Kind kind = Kind::Logical;
  Type type;
  // ResourceUnit carries an exact selected nominal slot, independently of
  // payload layout. Adapter must preserve this identity and permission profile.
  std::string resourceIdentity;
  Permissions permissions;
  std::vector<unsigned> path;
  // Exact selected public identity and active payload layouts for Variant.
  std::string variantIdentity = {};
  std::vector<std::vector<LayoutLeaf>> alternatives = {};
};
struct Layout {
  Type sourceType, concreteType;
  std::vector<LayoutLeaf> leaves;
};
struct LinkedCall {
  // Member calls point to a closed LinkedFunction symbol. Logical calls retain
  // the installed operation name, concrete static actuals, attributes and role.
  std::string target;
  bool logical = false;
};
struct LinkedFunction {
  std::string symbol;
  Body body; // Closed types/actuals; traversal instances have fresh ValueIds.
  std::map<uint32_t, Layout> values;
  std::map<std::vector<size_t>, LinkedCall>
      calls; // Nested instruction path: instruction, arm, instruction, ...
  // Promised result layouts in signature order. A body that always stops
  // returns nothing and still keeps this declared boundary, so callers compare
  // against it instead of an absent return.
  std::vector<Layout> results;
  // Exact symbol subject for collision checks across independently linked
  // units.
  std::string exactSubject;
  // Selected public types/labels before representation erasure. Frontend call
  // binding uses this boundary; body.signature is the concrete implementation.
  Signature logicalSignature;
};
struct DependencyRecord {
  std::string selection, interfaceIdentity, implementationIdentity;
  std::string interfaceFingerprint, implementationFingerprint;
  std::vector<std::string> paths, dependencies;
  // Exact canonical selection and hidden capture content. Compare content,
  // never fingerprints, when merging independently linked worlds.
  std::string normalizedSelection, captureIdentity, captureFingerprint;
};
struct Evidence {
  enum class State { Established, AcceptedPremise, Unavailable, Refuted };
  Facet facet;
  State state = State::Unavailable;
  std::string subject, ownerVersion, explanation;
};
struct LinkRequest {
  CheckedBody client;
  std::vector<Binding> bindings;
  Substitution arguments;
  // Separately checked owner-local bodies; declarations alone cannot execute.
  std::vector<CheckedBody> helpers = {};
  // Captured caller scope for actual static subjects. Never substitutes for a
  // helper's separately checked owner environment.
  std::optional<Environment> selectionEnvironment = std::nullopt;
};
class LinkedProgram {
  struct Data;
  std::shared_ptr<const Data> data;
  explicit LinkedProgram(std::shared_ptr<const Data>);
  friend llvm::Expected<LinkedProgram> link(LinkRequest, WorkBudget &);

public:
  const Environment &environment() const;
  const std::vector<LinkedFunction> &functions() const;
  const std::vector<DependencyRecord> &dependencies() const;
  const std::vector<Evidence> &evidence() const;
  const std::string &entry() const;
  const std::string &identity() const;
  const std::string &fingerprint() const;
};

// Resolve the bijection before checking/evaluating operands. Result maps each
// written operand index to its formal input index; empty labels are positional.
llvm::Expected<std::vector<unsigned>>
bindArguments(const Signature &, size_t operandCount,
              const std::vector<std::string> &writtenLabels);

llvm::Expected<Interface> formInterface(InterfaceDecl, Environment);
llvm::Expected<CheckedBody> checkBody(Body, Environment,
                                      std::vector<Import> imports = {});
llvm::Expected<CheckedComponent> checkComponent(ComponentDecl, Environment);
llvm::Expected<LinkedProgram> link(LinkRequest);
/// Share one invocation account across independently requested aliases. The
/// budget is borrowed for this call and is never retained by LinkedProgram.
llvm::Expected<LinkedProgram> link(LinkRequest, WorkBudget &);
// Resolve solely from captured installed-domain authority; unknown/open
// refuses.
llvm::Expected<std::string> resolvedDomain(const StaticTerm &,
                                           const Environment &);
llvm::Expected<Sort> sortOf(const StaticTerm &, const Environment &);
llvm::Expected<std::string> selectionIdentity(const StaticTerm &,
                                              const Environment &);
// True when this instruction sequence ends in an explicit terminal stop.
bool stopped(const std::vector<Instruction> &);
// True when this sequence cannot continue: it stops, or it ends in an
// exhaustive match or conditional whose every arm cannot continue. Such a
// sequence has no
// result — every caller, arm join and expansion drops its continuation — so
// the region containing it must return nothing and owes no result, fact or
// remaining-resource obligation.
bool terminal(const std::vector<Instruction> &);
std::string identity(const QualifiedDecl &);
std::string identity(const Type &);
std::string identity(const StaticTerm &);
bool sameType(const Type &, const Type &);

} // namespace zkc::frontend::library
#endif
