#ifndef ZKC_FRONTEND_SYNTAX_TREE_H
#define ZKC_FRONTEND_SYNTAX_TREE_H

#include "zkc/Source/Model.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"
#include <map>
#include <set>
#include <tuple>

namespace zkc::frontend::resolution {
struct Context;
}

namespace zkc::frontend::syntax {
// Authoring syntax owns unresolved calls and type expressions. It is never
// passed to a common-source, MLIR, artifact, or formal consumer.
// Preserve lexical category independently of decoded spelling. Quoted atoms
// are identities/data, never names to evaluate or substitute.
struct Atom : source::Node {
  enum class Kind { Name, Number, String };
  Kind kind = Kind::Name;
  std::string value;
};
struct StaticTerm {
  Atom root;
  source::Names members;
};
struct Type : source::Node {
  bool product = false;
  bool quoted = false;
  bool natural = false; // Sorted literal in checked-library type arguments.
  std::string name;
  std::vector<Type> arguments;
  source::Names members;
};
struct Parameter {
  std::string name;
  Type type;
};
struct OwnedParameter {
  std::string name, role;
  Type type;
};
struct OwnedResult {
  std::string role;
  Type type;
  std::string name;
};
struct StaticParameter : source::Node {
  std::string name;
  std::optional<std::string> sort; // `domain Sort`, without a capability.
  source::Names bounds;
};
struct Call : source::Node {
  std::string callee;
  bool quoted = false;
  std::vector<StaticTerm> staticTerms;
  std::vector<Atom> attributeAtoms, inputAtoms;
  bool qualified = false; // :: path, as opposed to an opaque exact name.
  std::optional<source::Names> staticArguments;
  source::Names attributes, inputs, outputs, argumentNames;
  std::optional<std::vector<Type>> annotation;
  std::optional<std::string> role; // Explicit protocol-local call.
  // The callee is an operator symbol over named operands. It is resolved from
  // the operands' types and then is the installed call, written flat.
  bool isOperator = false;
  bool destructure = false;
};
/// Small authoring expressions; these never become portable source records.
struct LexicalTraversal;
struct Expression : source::Node {
  enum class Kind {
    Name,
    Index,
    Boolean,
    Call,
    Vector,
    Get,
    Length,
    Struct,
    Product,
    Operator,
    Map,
    Fold
  };
  Kind kind = Kind::Name;
  bool quoted = false;
  std::vector<StaticTerm> staticTerms;
  std::vector<Atom> attributeAtoms;
  std::string name;
  bool qualified = false;
  std::optional<source::Names> staticArguments;
  source::Names attributes;
  // A struct construction names one field for each operand, in written order.
  source::Names fields;
  source::Names argumentNames;
  std::vector<Expression> operands;
  std::shared_ptr<LexicalTraversal> traversal;
};
struct Binding : source::Node {
  bool destructure = false;
  source::Names outputs;
  std::optional<std::vector<Type>> annotation;
  Expression expression;
  bool mutableBinding = false;
  bool assignment = false;
};
struct Exit {
  Expression expression;
};
struct Finish {
  source::Assignments values;
};
struct Invocation {
  std::string callee;
  source::Names inputs, outputs, resultNames;
};
struct Instruction;
using Body = std::vector<Instruction>;
struct LexicalTraversal {
  std::string state, element;
  source::Names captures;
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
  std::optional<Atom> countAtom;
  source::LoopCount count;
  source::Assignments carried;
  source::Names captures, outputs;
  Body body;
};
struct Conditional {
  bool explicitCaptures = false;
  Expression condition;
  Body thenBody, elseBody;
  bool explicitRegion = false;
  source::Names captures, outputs;
};
struct For {
  bool explicitCaptures = false;
  std::string induction;
  Expression lower, upper;
  Body body;
  bool explicitRegion = false;
  source::Assignments carried;
  source::Names captures, outputs;
};
struct MatchArm : source::Node {
  std::string alternative;
  source::Names payload;
  Body body;
};
struct Match {
  bool explicitCaptures = false;
  std::string input;
  source::Names captures, outputs;
  std::vector<MatchArm> arms;
};
struct ArrayTraversal {
  bool explicitCaptures = false;
  std::string element, input;
  source::Assignments carried;
  source::Names captures, outputs;
  Body body;
};
struct Instruction : source::Node {
  bool explicitSite = false;
  std::string site;
  std::variant<Call, Invocation, Finish, source::Message, source::Return,
               source::Yield, source::Stop, Exit, Placement, Loop, Binding,
               Conditional, For, Match, ArrayTraversal>
      value;
};
struct Function : source::Node {
  std::string name;
  bool explicitOrigin = false;
  source::Names effects;
  bool generic = false;
  std::vector<StaticParameter> parameters;
  // `where` clauses already use the common, ordered predicate syntax.
  std::vector<source::Requirement> requirements;
  std::vector<std::vector<StaticTerm>> requirementTerms;
  std::vector<Parameter> arguments;
  std::vector<Type> results;
  std::optional<Body> body;
  std::optional<source::LogicalOrigin> origin;
};
struct Protocol : source::Node {
  std::string name;
  bool generic = false;
  std::vector<StaticParameter> staticParameters;
  std::vector<source::Requirement> requirements;
  std::vector<std::vector<StaticTerm>> requirementTerms;
  struct DependencyArguments {
    source::Assignments arguments;
    std::vector<StaticTerm> terms;
  };
  std::map<std::string, DependencyArguments> dependencyArguments;
  source::Names roles, parameters;
  std::vector<OwnedParameter> arguments;
  std::vector<OwnedResult> results;
  std::vector<source::Dependency> dependencies;
  // Aliases of the dependencies whose protocol was written quoted.
  std::set<std::string> quotedDependencies;
  std::optional<Body> body;
};
struct RelationImport : source::Node {
  std::string name, family, path;
};
/// A named group of typed fields. A struct value is rewritten into its leaf
/// values, so a struct never becomes a portable source record. A checked
/// struct can be constructed only inside its named constructor functions.
struct Struct : source::Node {
  std::string name;
  bool checked = false;
  std::vector<StaticParameter> parameters;
  std::vector<Parameter> fields;
  source::Names constructors;
  std::set<std::string> quotedConstructors;
};
/// A named, ordered requirement list over its parameters. A use is replaced by
/// these requirements, so a bundle never becomes a portable source record.
struct Enum : source::Node {
  std::string name;
  std::vector<StaticParameter> parameters;
  std::vector<Parameter> alternatives;
};
struct Bundle : source::Node {
  std::vector<std::vector<StaticTerm>> requirementTerms;
  std::string name;
  source::Names parameters;
  std::vector<source::Requirement> requirements;
};
struct Constant : source::Node {
  std::string name;
  Expression expression;
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
  std::string interface;
  bool quotedInterface = false;
  std::vector<StaticParameter> parameters;
};
struct LibrarySelection : source::Node {
  std::string name;
  LibraryTerm target;
  bool sealed = false;
};
struct LibraryLink : source::Node {
  std::string name, client;
  bool quotedClient = false;
  std::vector<LibraryTerm> arguments;
};
struct Module : source::Node {
  // A self-contained common-carrier representation, not a source library.
  // This is explicit input syntax, never trusted compiler provenance.
  bool carrier = false;
  std::shared_ptr<const resolution::Context> project;
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
  std::map<std::string, Protocol::DependencyArguments> entryArguments;
  // Metadata for authoring-only static sites whose common records use strings.
  std::map<std::string, std::vector<Atom>> instanceParameterAtoms;
  std::map<std::string, StaticTerm> instanceProtocolTerms;
  std::map<std::string, std::vector<StaticTerm>> configurationTerms;
  std::map<std::string, Atom> relationViewHeights;
  // Clause references written quoted, by the name of the declaration that
  // holds them: a configuration's base, a relation view's relation, an entry's
  // instance, an instance's dependencies by alias and its ingress selectors by
  // parameter and role. A quoted spelling names the declaration in scope.
  std::set<std::string> quotedBases, quotedRelations, quotedInstances;
  std::set<std::pair<std::string, std::string>> quotedInstanceDependencies;
  std::set<std::tuple<std::string, std::string, std::string>> quotedSelectors;
  std::vector<RelationImport> imports;
  std::vector<source::RelationDeclaration> relations;
  std::vector<source::RelationView> relationViews;
  std::optional<std::string> profile;
  std::vector<source::OperationBinding> bindings;
  std::vector<Bundle> bundles;
  std::vector<Struct> structs;
  std::vector<Enum> enums;
  std::vector<Function> functions;
  std::vector<Protocol> protocols;
  std::vector<source::Configuration> configurations;
  std::vector<source::Instance> instances;
  std::vector<source::Entry> entries;
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
