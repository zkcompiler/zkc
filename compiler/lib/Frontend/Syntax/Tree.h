#ifndef ZKC_FRONTEND_SYNTAX_TREE_H
#define ZKC_FRONTEND_SYNTAX_TREE_H

#include "Names.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"
#include <map>
#include <set>
#include <tuple>

namespace zkc::frontend::syntax {
// Authoring syntax owns unresolved calls and type expressions. It is never
// passed to a common-source, MLIR, artifact, or formal consumer.
struct StaticTerm {
  Atom root;
  source::Names members;
  std::vector<StaticTerm> arguments = {};
};
using StaticTerms = std::vector<StaticTerm>;
using StaticAssignments = std::vector<std::pair<std::string, StaticTerm>>;
struct Type : source::Node {
  bool product = false;
  // Category of the root: a reference, a sorted natural literal in a type
  // argument, or an exact quoted identity.
  Atom::Kind kind = Atom::Kind::Name;
  std::string name;
  std::vector<Type> arguments;
  source::Names members;
  bool quoted() const { return kind == Atom::Kind::String; }
  bool natural() const { return kind == Atom::Kind::Number; }
};
inline Type typeExpression(const StaticTerm &term) {
  Type result;
  result.location = term.root.location;
  result.kind = term.root.kind;
  result.name = term.root.value;
  result.members = term.members;
  for (const auto &argument : term.arguments)
    result.arguments.push_back(typeExpression(argument));
  return result;
}
inline StaticTerm staticExpression(const Type &type) {
  StaticTerm result;
  result.root.location = type.location;
  result.root.kind = type.kind;
  result.root.value = type.name;
  result.members = type.members;
  for (const auto &argument : type.arguments)
    result.arguments.push_back(staticExpression(argument));
  return result;
}
/// The common carrier's spelling of a resolved static term. Semantic owners
/// call this after resolution and substitution; syntax never stores it.
inline std::string staticSpelling(const StaticTerm &term) {
  std::string result = term.root.value;
  for (const auto &member : term.members)
    result += "." + member;
  if (!term.arguments.empty()) {
    result += "<";
    for (const auto &argument : term.arguments) {
      if (result.back() != '<')
        result += ",";
      result += staticSpelling(argument);
    }
    result += ">";
  }
  return result;
}
inline source::Names staticSpellings(llvm::ArrayRef<StaticTerm> terms) {
  source::Names result;
  for (const auto &term : terms)
    result.push_back(staticSpelling(term));
  return result;
}
/// A requirement over static terms. Equality has no predicate.
struct Requirement : source::Node {
  std::optional<Reference> predicate;
  StaticTerms arguments;
};
/// The common requirement record of a resolved requirement.
inline source::Requirement commonRequirement(const Requirement &requirement) {
  source::Requirement result;
  result.location = requirement.location;
  result.predicate =
      requirement.predicate ? encode(*requirement.predicate) : "=";
  result.arguments = staticSpellings(requirement.arguments);
  return result;
}
struct Parameter {
  std::string name;
  Type type;
};
struct OwnedParameter {
  std::string name, role;
  Type type;
  // Mathematical availability; ordinary located ports use the single role.
  source::Names availability = {};
};
struct OwnedResult {
  std::string role;
  Type type;
  std::string name;
  source::Names availability = {};
};
struct StaticParameter : source::Node {
  std::string name;
  std::optional<std::string> sort; // `domain Sort`, without a capability.
  std::vector<Reference> bounds;
};
struct LexicalTraversal;
/// Small authoring expressions; these never become portable source records.
struct Expression : source::Node {
  enum class Kind {
    Name,
    Index,
    Boolean,
    Call,
    Vector,
    Get,
    Field,
    TupleField,
    Length,
    Struct,
    Product,
    Operator,
    Map,
    Fold
  };
  Kind kind = Kind::Name;
  // The value, callee or record constructor of Name, Call and Struct.
  Reference reference;
  // The selected field or ordinal, a literal, or an operator symbol.
  std::string name;
  std::optional<StaticTerms> staticArguments;
  std::vector<Atom> attributes;
  // A struct construction names one field for each operand, in written order.
  source::Names fields;
  source::Names argumentNames;
  std::vector<Expression> operands;
  std::shared_ptr<LexicalTraversal> traversal;
};
/// A static projection applied to the first operand, independent of whether
/// that receiver is a place or a computed value.
inline std::optional<Projection> projection(const Expression &expression,
                                            bool brackets = true) {
  using K = Expression::Kind;
  Projection step;
  step.location = expression.location;
  if (expression.kind == K::Field) {
    step.kind = Projection::Kind::Field;
    step.key = expression.name;
  } else if (expression.kind == K::TupleField) {
    step.kind = Projection::Kind::Product;
    step.key = expression.name;
  } else if (brackets && expression.kind == K::Get &&
             expression.operands.size() == 2 &&
             expression.operands[1].kind == K::Index) {
    step.kind = Projection::Kind::Index;
    step.key = expression.operands[1].name;
  } else
    return std::nullopt;
  return step;
}
/// A place candidate performs no computation. Flat-call operands exclude
/// brackets so their occurrence/site identity is stable.
inline std::optional<Place> placeCandidate(const Expression &expression,
                                           bool brackets = true) {
  if (expression.kind == Expression::Kind::Name) {
    Place result;
    result.root = expression.reference;
    result.location = expression.location;
    return result;
  }
  auto step = projection(expression, brackets);
  if (!step || expression.operands.empty())
    return std::nullopt;
  auto result = placeCandidate(expression.operands.front(), brackets);
  if (!result)
    return std::nullopt;
  result->steps.push_back(std::move(*step));
  result->location = expression.location;
  return result;
}
/// The expression that reads a place: its root reference and selections.
inline Expression placeExpression(const Place &place) {
  Expression result;
  result.reference = place.root;
  result.location = place.root.location;
  for (const auto &step : place.steps) {
    Expression next;
    next.location = step.location;
    next.kind = step.kind == Projection::Kind::Field ? Expression::Kind::Field
                : step.kind == Projection::Kind::Product
                    ? Expression::Kind::TupleField
                    : Expression::Kind::Get;
    next.operands.push_back(std::move(result));
    if (step.kind == Projection::Kind::Index) {
      Expression index;
      index.kind = Expression::Kind::Index;
      index.name = step.key;
      index.location = step.location;
      next.operands.push_back(std::move(index));
    } else
      next.name = step.key;
    result = std::move(next);
  }
  result.location = place.location ? place.location : result.location;
  return result;
}
struct Binding : source::Node {
  bool destructure = false;
  source::Names outputs;
  std::optional<std::vector<Type>> annotation;
  Expression expression;
  bool mutableBinding = false;
  std::optional<Place> assignment;
};
/// A flat call statement over places. Parser site numbering counts it as one
/// authored instruction whatever its operands' projection structure.
struct Call : source::Node {
  // The callee, or, for an operator, nothing: its symbol selects the target
  // from the operands' nominal types.
  Reference callee;
  std::optional<std::string> operatorSymbol;
  std::optional<StaticTerms> staticArguments;
  std::vector<Atom> attributes;
  Places inputs;
  source::Names outputs, argumentNames;
  std::optional<std::vector<Type>> annotation;
  std::optional<std::string> role; // Explicit protocol-local call.
  bool destructure = false;
};
struct Exit {
  Expression expression;
};
struct Finish {
  PlaceAssignments values;
};
struct Invocation {
  std::string callee; // A dependency alias of the enclosing protocol.
  Places inputs;
  source::Names outputs, resultNames;
};
struct Instruction;
using Body = std::vector<Instruction>;
struct LexicalTraversal {
  std::string state, element;
  Places captures;
  Body body;
};
struct Placement {
  std::string role;
  source::Names outputs;
  bool destructure = false;
  std::optional<Type> annotation;
  Body body;
};
struct Loop {
  bool explicitCaptures = false;
  Atom count; // A natural literal, parameter or constant reference.
  PlaceAssignments carried;
  Places captures;
  source::Names outputs;
  Body body;
};
struct Conditional {
  bool explicitCaptures = false;
  Expression condition;
  Body thenBody, elseBody;
  bool explicitRegion = false;
  Places captures;
  source::Names outputs;
};
struct For {
  bool explicitCaptures = false;
  std::string induction;
  Expression lower, upper;
  Body body;
  bool explicitRegion = false;
  PlaceAssignments carried;
  Places captures;
  source::Names outputs;
};
struct MatchArm : source::Node {
  std::string alternative;
  source::Names payload;
  Body body;
};
struct Match {
  bool explicitCaptures = false;
  Place input;
  Places captures;
  source::Names outputs;
  std::vector<MatchArm> arms;
};
struct ArrayTraversal {
  bool explicitCaptures = false;
  std::string element;
  Place input;
  PlaceAssignments carried;
  Places captures;
  source::Names outputs;
  Body body;
};
struct Message {
  std::string schema, sender, receiver, output;
  Place input;
};
struct Return {
  Places values;
};
struct Yield {
  Places values;
};
struct Query {
  std::string role, root;
  source::Names outputs;
};
struct Guard {
  std::string role;
  Place condition;
};
struct Instruction : source::Node {
  bool explicitSite = false;
  std::string site;
  std::variant<Call, Invocation, Finish, Message, Return, Yield, source::Stop,
               Exit, Placement, Loop, Binding, Conditional, For, Match,
               ArrayTraversal, Query, Guard>
      value;
};
struct Function : source::Node {
  std::string name;
  bool explicitOrigin = false;
  source::Names effects;
  bool generic = false;
  std::vector<StaticParameter> parameters;
  std::vector<Requirement> requirements;
  std::vector<Parameter> arguments;
  std::vector<Type> results;
  std::optional<Body> body;
  std::optional<source::LogicalOrigin> origin;
  // Fixed language hook; the signature supplies nominal operand heads.
  std::optional<std::string> operatorHook = {};
};
/// A protocol dependency. A specialised generic dependency writes its named
/// static arguments.
struct Dependency : source::Node {
  std::string name;
  Reference protocol;
  std::optional<StaticAssignments> arguments;
  source::Assignments agreements;
};
struct Protocol : source::Node {
  std::string name;
  bool generic = false;
  std::vector<StaticParameter> staticParameters;
  std::vector<Requirement> requirements;
  source::Names roles, parameters;
  std::vector<OwnedParameter> arguments;
  std::vector<OwnedResult> results;
  std::vector<Dependency> dependencies;
  struct Root : source::Node {
    std::string name;
    Reference service;
    source::Names owners;
  };
  struct MathematicalBody {
    std::vector<Root> roots;
    Body instructions;
  };
  // Distinct body kinds prevent ordinary ownership/lowering from accepting a
  // mathematical graph implicitly. Syntax-only visitors may use instructions.
  std::variant<std::optional<Body>, MathematicalBody> body;
  Body *instructions() {
    if (auto *ordinary = std::get_if<std::optional<Body>>(&body))
      return *ordinary ? &**ordinary : nullptr;
    return &std::get<MathematicalBody>(body).instructions;
  }
  const Body *instructions() const {
    if (auto *ordinary = std::get_if<std::optional<Body>>(&body))
      return *ordinary ? &**ordinary : nullptr;
    return &std::get<MathematicalBody>(body).instructions;
  }
};
struct RelationImport : source::Node {
  std::string name, family, path;
};
/// A derived relation view. A symbolic height names a natural constant.
struct RelationView : source::Node {
  std::string name, kind, staging;
  Reference relation;
  std::optional<Atom> height;
};
/// A named group of typed fields. A struct value is rewritten into its leaf
/// values, so a struct never becomes a portable source record. A checked
/// struct can be constructed only inside its named constructor functions.
struct Struct : source::Node {
  std::string name;
  bool checked = false;
  std::vector<StaticParameter> parameters;
  std::vector<Parameter> fields;
  std::vector<Reference> constructors;
};
struct Enum : source::Node {
  std::string name;
  std::vector<StaticParameter> parameters;
  std::vector<Parameter> alternatives;
};
/// A named, ordered requirement list over its parameters. A use is replaced by
/// these requirements, so a bundle never becomes a portable source record.
struct Bundle : source::Node {
  std::string name;
  source::Names parameters;
  std::vector<Requirement> requirements;
};
struct Constant : source::Node {
  std::string name;
  Expression expression;
};
struct Configuration : source::Node {
  std::string name;
  Reference base;
  StaticAssignments arguments;
  source::Assignments implementations;
};
struct IngressSelector {
  std::string role;
  Reference function;
  source::Names arguments;
};
/// An instance natural parameter, or an ingress family with its natural bound.
struct InstanceParameter {
  Atom value;
  std::optional<std::vector<IngressSelector>> ingress;
};
struct Instance : source::Node {
  std::string name;
  // The protocol, optionally followed by dependency aliases of a selected
  // protocol.
  Reference protocol;
  std::vector<std::pair<std::string, InstanceParameter>> parameters;
  std::vector<std::pair<std::string, Reference>> dependencies;
  source::Assignments roles;
};
struct Entry : source::Node {
  std::string name;
  Reference instance;
  std::optional<StaticAssignments> arguments;
};
// Checked library declarations retain authoring types and bodies until the
// separate typed library checker has formed and linked them.
struct LibraryIdentity : source::Node {
  std::string nameSpace, name, version, resolution;
};
struct ModuleDeclaration : source::Node {
  std::string name;
};
struct LibraryDependency : source::Node {
  std::string name;
  LibraryIdentity identity;
};
struct Use : source::Node {
  source::Names path;
  std::string name;
  bool exported = false;
};
struct LibraryAssociation : source::Node {
  std::string name, captured;
};
struct LibraryTerm : source::Node {
  Atom root;
  std::vector<LibraryTerm> arguments;
  source::Names members;
  bool applied = false;
};
struct LibraryTypeMember : source::Node {
  std::string name;
  bool copy = false, drop = false;
  std::optional<Type> representation;
};
struct LibraryStaticMember : source::Node {
  std::string name, sort, domain;
  std::optional<LibraryTerm> equation;
};
struct LibraryFacet : source::Node {
  std::string owner, name;
  bool required = true;
};
struct LibraryInterface : source::Node {
  std::string name;
  std::vector<LibraryTypeMember> types;
  std::vector<LibraryStaticMember> statics;
  std::vector<LibraryFacet> facets;
  std::vector<Function> functions;
};
struct LibraryComponent : LibraryInterface {
  Reference interface;
  std::vector<StaticParameter> parameters;
};
struct LibrarySelection : source::Node {
  std::string name;
  LibraryTerm target;
  bool sealed = false;
};
struct LibraryLink : source::Node {
  std::string name;
  Reference client;
  std::vector<LibraryTerm> arguments;
};
struct Module : source::Node {
  std::vector<ModuleDeclaration> modules;
  std::vector<LibraryDependency> dependencies;
  std::vector<Use> uses;
  // Names declared pub in this source module, before identity resolution.
  source::Names exports;
  std::vector<LibraryIdentity> libraryIdentities;
  std::vector<LibraryAssociation> libraryAssociations;
  std::vector<LibraryInterface> libraryInterfaces;
  std::vector<LibraryComponent> libraryComponents;
  std::vector<LibraryLink> libraryLinks;
  std::vector<LibrarySelection> librarySelections;
  std::vector<Constant> constants;
  std::vector<RelationImport> imports;
  std::vector<source::RelationDeclaration> relations;
  std::vector<RelationView> relationViews;
  std::vector<source::OperationBinding> bindings;
  std::vector<Bundle> bundles;
  std::vector<Struct> structs;
  std::vector<Enum> enums;
  std::vector<Function> functions;
  std::vector<Protocol> protocols;
  std::vector<Configuration> configurations;
  std::vector<Instance> instances;
  std::vector<Entry> entries;
};
using Content = std::variant<Module, source::Construction>;
struct ParseDiagnostic : source::Node {
  std::string code, message;
};
struct ParseResult {
  std::optional<Content> content;
  std::vector<ParseDiagnostic> diagnostics;
  bool complete() const { return content.has_value() && diagnostics.empty(); }
};
ParseResult parseRecoverable(llvm::StringRef text, llvm::StringRef filename,
                             uint32_t file = 0);
llvm::Expected<Content> parse(llvm::StringRef text, llvm::StringRef filename,
                              uint32_t file = 0);
llvm::json::Value inspect(const Content &);
} // namespace zkc::frontend::syntax
#endif
