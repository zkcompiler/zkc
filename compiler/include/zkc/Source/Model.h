#ifndef ZKC_SOURCE_MODEL_H
#define ZKC_SOURCE_MODEL_H

#include "zkc/Contracts/Binding.h"

#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/ADT/StringRef.h"
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>

namespace zkc::relation {
class R1CS;
class AIR;
} // namespace zkc::relation

namespace zkc::source {

struct Span {
  size_t offset = 0;
  size_t length = 0;
  // Snapshot-local source file. Zero is the root of a single-file input.
  // This is diagnostic provenance, never a nominal or transcript identity.
  uint32_t file = 0;
};

/// Optional diagnostic origin in the enclosing document's spelling. It is not
/// serialized, trusted evidence, a symbol, or a transcript identity. Transforms
/// copy origins from their actual source nodes; generated nodes may lack one.
struct Node {
  std::optional<Span> location;
};

using Names = std::vector<std::string>;
using Assignments = std::vector<std::pair<std::string, std::string>>;

struct Parameter {
  std::string name;
  std::string type;
};
struct OwnedParameter {
  std::string name;
  std::string role;
  std::string type;
};
struct OwnedResult {
  std::string role;
  std::string type;
};

// Names, logical type spellings, and static terms remain unresolved here.
// Structural typing of the C++ model does not establish source admission.
struct Operation {
  std::string callee;
  Names staticArguments;
  Names attributes;
  Names inputs;
  Names outputs;
};
struct LocalCall {
  std::string role; // Empty only in a projected participant.
  std::string callee;
  Names inputs;
  Names outputs;
};
/// A role-free, acyclic application. Static arguments are eliminated by
/// specialization before common MLIR admission.
struct AlgorithmCall {
  std::string callee;
  Names inputs;
  Names outputs;
  Names staticArguments = {};
};
struct ProtocolCall {
  std::string
      callee; // Dependency alias in common source, symbol in a participant.
  Names inputs;
  Names outputs;
};
struct Message {
  std::string schema;
  std::string sender;
  std::string receiver;
  std::string input;
  std::string output;
};
struct Send {
  std::string schema;
  std::string peer;
  std::string input;
};
struct Receive {
  std::string schema;
  std::string peer;
  std::string output;
  std::string type;
};
struct Release {
  Names values;
};
struct Return {
  Names values;
};
struct Yield {
  Names values;
};
struct Stop {
  std::string role;
  std::string reason;
};
struct Incomplete {};

struct Instruction;
using Body = std::vector<Instruction>;
struct LoopCount {
  enum class Kind { Constant, Parameter };
  Kind kind = Kind::Constant;
  std::string value;
};
struct Loop {
  LoopCount count;
  Assignments carried;
  Names captures;
  Body body;
  Names outputs;
};

/// Role-local structured control. Regions have explicit captures and yield
/// their ordered results; protocol interaction remains outside these regions.
struct Conditional {
  std::string condition;
  Names captures;
  Body thenBody, elseBody;
  Names outputs;
};
struct For {
  std::string induction, lower, upper;
  Assignments carried;
  Names captures;
  Body body;
  Names outputs;
};

struct VariantConstruct {
  std::string type, alternative;
  Names payload;
  std::string output;
};
struct MatchArm {
  std::string alternative;
  Names payload;
  Body body;
};
struct Match {
  std::string input;
  Names captures;
  std::vector<MatchArm> arms;
  Names outputs;
};

struct Instruction : Node {
  using Value =
      std::variant<Operation, LocalCall, ProtocolCall, Message, Send, Receive,
                   Return, Yield, Stop, Incomplete, Loop, Release,
                   AlgorithmCall, Conditional, For, VariantConstruct, Match>;
  std::string site; // Empty for return/yield/release; scoped to its definition
                    // otherwise.
  Value value;

  template <typename T> const T *get() const { return std::get_if<T>(&value); }
  template <typename T> T *get() { return std::get_if<T>(&value); }
  llvm::StringRef kind() const;
  bool isTerminator() const;
};

struct LogicalOrigin {
  std::string definition;
  Assignments arguments;
};
struct Function : Node {
  std::string name;
  std::vector<Parameter> arguments;
  Names results;
  std::optional<Body> body; // Absent means an explicit external declaration.
  std::optional<LogicalOrigin> origin; // Required for explicit-binding modules.
};
struct Dependency : Node {
  std::string name;
  std::string protocol;
  Assignments agreements;
};
struct Protocol : Node {
  std::string name;
  Names roles;
  Names parameters;
  std::vector<OwnedParameter> arguments;
  std::vector<OwnedResult> results;
  std::vector<Dependency> dependencies;
  std::optional<Body> body;
};
/// Checked entry-only selection from an ordinary role-local function. The
/// function consumes that role's actual entry arguments and returns one index.
struct FamilySelector {
  std::string role, function;
  Names arguments;
  bool operator==(const FamilySelector &other) const {
    return role == other.role && function == other.function &&
           arguments == other.arguments;
  }
};
struct FamilyIngress {
  std::string bound;
  std::vector<FamilySelector> selectors;
  bool operator==(const FamilyIngress &other) const {
    return bound == other.bound && selectors == other.selectors;
  }
  bool operator!=(const FamilyIngress &other) const {
    return !(*this == other);
  }
};
using ParameterBinding = std::variant<std::string, FamilyIngress>;
using ParameterBindings = std::vector<std::pair<std::string, ParameterBinding>>;

struct Instance : Node {
  std::string name;
  std::string protocol;
  ParameterBindings parameters;
  Assignments dependencies;
  Assignments roles;
};
struct Entry : Node {
  std::string name;
  std::string instance;
};
/// Application of an installed logical contract, with an optional physical
/// implementation. A record alone is not evidence of admission. The symbol is
/// a reference, not a transcript/session/resource identity.
struct OperationBinding : Node {
  std::string name;
  protocol::BindingApplication application;
};

struct StaticParameter {
  std::string name;
  std::string sort;
};
struct Requirement : Node {
  std::string predicate;
  Names arguments;
};
struct GenericFunction : Node {
  std::string name;
  std::vector<StaticParameter> parameters;
  std::vector<Requirement> requirements;
  std::vector<Parameter> arguments;
  Names results;
  Body body;
};
struct Configuration : Node {
  std::string name;
  std::string base;
  Assignments arguments;
  Assignments implementations;
};

/// Resolved immutable compilation input. Paths belong only to syntax/loading;
/// this record contains the exact typed family payload and ordered layout.
struct RelationDeclaration : Node {
  std::string name;
  std::variant<std::shared_ptr<const relation::R1CS>,
               std::shared_ptr<const relation::AIR>>
      value;
};
struct RelationView : Node {
  std::string name, relation;
  std::string kind;    // multilinear or arithmetic
  std::string staging; // specialized or public_matrices
  uint32_t height = 0; // Finite AIR arithmetic schedule only.
};

/// Common source remains open until specialization and admission. Generic
/// definitions are declarations, not runtime calls. Source section order is
/// retained for exact-source custody; symbol tables are derived analyses.
struct Module : Node {
  std::vector<OperationBinding> bindings;
  std::vector<Function> functions;
  std::vector<Protocol> protocols;
  std::vector<Instance> instances;
  std::vector<Entry> entries;
  std::vector<GenericFunction> definitions;
  std::vector<Configuration> configurations;
  std::vector<RelationDeclaration> relations;
  std::vector<RelationView> relationViews;
  // Preserve an explicitly empty library envelope at the interchange boundary.
  bool library = false;
  bool isLibrary() const {
    return library || !definitions.empty() || !configurations.empty();
  }
};

/// Projected artifacts reuse local bodies and instruction structure, but are a
/// distinct input kind. They cannot masquerade as an authored common module.
struct Participant : Node {
  std::string name;
  std::string instance;
  std::string role;
  ParameterBindings parameters;
  std::vector<Parameter> arguments;
  Names results;
  Body body;
};
struct ParticipantEntry : Node {
  std::string name;
  Assignments participants;
};
struct Participants : Node {
  enum class Stage { Logical, Physical };
  Stage stage = Stage::Logical;
  std::vector<OperationBinding> bindings;
  std::vector<Function> functions;
  std::vector<Participant> participants;
  std::vector<ParticipantEntry> entries;
};

struct PublicBinding : Node {
  std::string name;
  Assignments ports;
};
struct Construction : Node {
  enum class Identity { Exact, Normalized };
  Identity identity = Identity::Normalized;
  std::string entry;
  std::string producer;
  std::string validator;
  std::vector<PublicBinding> publicBindings;
  std::string randomness;
  Assignments draws;
  std::string acceptance;
  std::string suite;
};

using Content = std::variant<Module, Participants, Construction>;

/// Preorder, including declarations and nested instruction bodies. Traversal
/// references are borrowed; do not mutate container structure from callbacks.
void walk(const Content &, llvm::function_ref<void(const Node &)>);
void walk(Content &, llvm::function_ref<void(Node &)>);
void walk(const Body &, llvm::function_ref<void(const Instruction &)>);
void walk(Body &, llvm::function_ref<void(Instruction &)>);

} // namespace zkc::source
#endif
