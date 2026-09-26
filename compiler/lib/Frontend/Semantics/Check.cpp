#include "Check.h"
#include "../Model/Libraries.h"
#include "../Resolution/Project.h"
#include "../Static/Domains.h"
#include "../Syntax/Lexer.h"
#include "../Syntax/Tree.h"
#include "../Syntax/Types.h"
#include "LibraryEntries.h"
#include "Local.h"
#include "Operators.h"
#include "Protocols.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Source/Codec.h"
#include "zkc/Source/Relations.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/StringExtras.h"
#include <functional>
#include <map>
#include <set>
#include <type_traits>

using namespace llvm;
namespace zkc::frontend::semantics {
using namespace syntax;
namespace {
/// Resolve the two explicit convenience profiles while forming source types.
/// There is no later signature rewrite: records and their leaves see the same
/// selected domains as ordinary logical ports and expression annotations.
StringRef profileIdentity(StringRef profile, StringRef kind) {
  if (profile != "arkworks.multilinear.bls12-381/1" &&
      profile != "arkworks.bls12-381/1")
    return {};
  if (kind == "group" || kind == "groups")
    return profile == "arkworks.bls12-381/1" ? "bls12-381.g1" : "";
  if (kind == "nonce")
    return profile == "arkworks.bls12-381/1" ? "bls12-381.fr" : "";
  if (kind == "transcript")
    return "merlin3.bls12-381.fr64be/1";
  if (is_contained(ArrayRef<StringRef>{"commitment", "proof", "opening_state",
                                       "prover_key", "verifier_key"},
                   kind))
    return "multilinear.kzg.bls12-381/1";
  return is_contained(
             ArrayRef<StringRef>{"field", "table", "point", "round", "rng"},
             kind)
             ? "bls12-381.fr"
             : "";
}
bool knownProfile(StringRef profile) {
  return profile == "arkworks.multilinear.bls12-381/1" ||
         profile == "arkworks.bls12-381/1";
}
/// A convenience profile is source notation only: it becomes the explicit
/// declarations the carrier always holds
/// (docs/compiler/carrier-consolidation.md).
void elaborateProfile(source::Module &module, StringRef profile) {
  std::set<std::string> names;
  for (const auto &b : module.bindings)
    names.insert(b.name);
  for (const auto &f : module.functions)
    names.insert(f.name);
  for (const auto &p : module.protocols)
    names.insert(p.name);
  for (const auto &i : module.instances)
    names.insert(i.name);
  for (const auto &e : module.entries)
    names.insert(e.name);
  std::map<std::string, std::string> operations;
  for (auto &f : module.functions) {
    if (!f.origin)
      f.origin = source::LogicalOrigin{f.name, {}};
    if (!f.body)
      continue;
    for (auto &instruction : *f.body) {
      auto *op = instruction.get<source::Operation>();
      if (!op)
        continue;
      auto existing = operations.find(op->callee);
      if (existing != operations.end()) {
        op->callee = existing->second;
        continue;
      }
      // Formation belongs to admission, not parsing: incomplete/unknown
      // contracts must remain editable and formatable as structural source.
      source::OperationBinding binding;
      binding.location = instruction.location;
      binding.name = op->callee;
      while (!names.insert(binding.name).second)
        binding.name += "_";
      binding.application.contract = op->callee;
      StringRef key = binding.application.contract;
      if (key.starts_with("pcs."))
        binding.application.arguments = {"multilinear.kzg.bls12-381/1"};
      else if (key.starts_with("curve.") && key != "curve.response")
        binding.application.arguments = {"bls12-381.g1"};
      else if (key.starts_with("transcript.")) {
        binding.application.arguments = {"merlin3.bls12-381.fr64be/1"};
        if (key.starts_with("transcript.observe.")) {
          std::string payload = key.drop_front(19).str();
          auto identity = profileIdentity(profile, payload);
          if (!identity.empty())
            payload += ":" + identity.str();
          auto parsed = protocol::parseBoundType(payload, false);
          if (parsed) {
            if (!parsed->identity.empty())
              binding.application.arguments.push_back(parsed->identity);
            binding.application.arguments.push_back(
                protocol::defaultCodec(*parsed).str());
          } else {
            consumeError(parsed.takeError());
          }
        }
      } else if (key != "bool.and" && key != "control.require" &&
                 !key.starts_with("index.") && !key.starts_with("indices."))
        binding.application.arguments = {"bls12-381.fr"};
      // Select the actual profile backend; never infer the PCS scheme from its
      // old module name or silently substitute a different representation.
      binding.application.implementation =
          (key.starts_with("index.") || key.starts_with("indices.")
               ? "native/"
               : "arkworks/") +
          binding.application.contract;
      operations.emplace(op->callee, binding.name);
      op->callee = binding.name;
      module.bindings.push_back(std::move(binding));
    }
  }
}

// A signature pattern contains nominal terms, never physical representations.
struct Signature {
  std::vector<source::StaticParameter> parameters;
  source::Names inputs, outputs;
  std::vector<source::Requirement> requirements;
  // Authored positions. `inputs` and `outputs` above are the flat leaves; a
  // signature without structs leaves these empty.
  Shapes inputShapes, outputShapes;
};
struct StructInfo {
  const Struct *declaration = nullptr;
  std::vector<source::StaticParameter> parameters;
  std::map<std::string, std::string> scope;
  AggregateShape shape; // Over the struct's own parameters.
  bool resolved = false, resolving = false;
};
Shapes authored(const Shapes &shapes, size_t flat) {
  return shapes.empty() ? Shapes(flat) : shapes;
}
using Sorts = std::map<std::string, std::string>;
using Values = std::map<std::string, std::string>;

class Checker {
  model::Module &model;
  ScopeId activeScope{0};
  DeclId activeOwner;
  DeclId id(StringRef name) const { return model.lookup({0}, name); }
  Signature getSignature(StringRef name) { return projectSignature(id(name)); }
  Signature protocolSignature(StringRef name) {
    return projectSignature(id(name));
  }
  const Module &syntax;
  const Module *original;
  StringRef text, filename;
  source::Module module;
  source::Module generated;
  const LibraryEmission &linked;
  std::vector<const syntax::Function *> functions;
  std::map<std::string, const LibraryEntry *> entries;

  std::string code, message;
  std::optional<source::Span> failure;
  std::map<DeclId, Signature> signatures;
  std::set<std::string> algorithms, genericAlgorithms;
  std::map<std::string, std::optional<source::Span>> declared;
  std::map<std::string, const source::Configuration *> configurations;
  std::map<std::string, const Bundle *> bundles;
  std::map<std::string, StructInfo> structs;
  std::map<std::string, LocalAggregates> structParameters;
  std::set<std::string> resolving;
  std::map<std::pair<std::string, std::string>, std::string> profileCalls;

  // A convenience profile belongs to its authored root. Imported and child
  // definitions keep explicit domains and implementations regardless of caller.
  bool usesProfile(const source::Node &node) const {
    const auto &project = *model.resolution;
    return syntax.profile && node.location && !project.owners.empty() &&
           node.location->file == project.owners.front().root;
  }

  void predeclare() {
    auto add = [&](const auto &node, Declaration::Kind kind) {
      if (id(node.name).valid()) {
        fail(node, "source-duplicate-symbol",
             "duplicate declaration '" + node.name + "'");
        return;
      }
      model.add(kind, {0}, node.name, node.location);
    };
    for (const auto &d : syntax.structs)
      add(d, Declaration::Kind::Record);
    for (const auto *d : functions)
      add(*d, Declaration::Kind::Function);
    for (const auto &d : syntax.protocols)
      add(d, Declaration::Kind::Protocol);
    for (const auto &d : syntax.bundles)
      add(d, Declaration::Kind::Bundle);
    for (const auto &d : syntax.bindings)
      add(d, Declaration::Kind::Binding);
    for (const auto &d : syntax.configurations)
      add(d, Declaration::Kind::Configuration);
    for (const auto &d : syntax.instances)
      add(d, Declaration::Kind::Instance);
    for (const auto &d : syntax.entries)
      add(d, Declaration::Kind::Entry);
    for (const auto &d : syntax.relations)
      add(d, Declaration::Kind::Relation);
    for (const auto &d : syntax.relationViews)
      add(d, Declaration::Kind::RelationView);
    if (original) {
      for (const auto &p : original->protocols)
        if (p.generic)
          add(p, Declaration::Kind::Protocol);
      for (const auto &c : original->constants)
        if (!id(c.name).valid())
          add(c, Declaration::Kind::Constant);
    }
    if (!good())
      return;
    auto parameters = [&](DeclId owner, const auto &parameters) {
      ScopeId scope = model.declarations[owner.index].members;
      for (const auto &p : parameters) {
        // The explicit common carrier shares a spelling namespace between
        // bound domain terms and installed identities. Refuse capture instead
        // of silently turning a quoted concrete domain into a parameter.
        if (StringRef(p.name).contains('.') ||
            !protocol::installedIdentitySort(p.name).empty()) {
          fail(p, "source-static-name",
               "domain parameter must be undotted and distinct from installed "
               "identities");
          return;
        }
        if (model.lookup(scope, p.name).valid()) {
          fail(p, "generic-duplicate-parameter", "duplicate static parameter");
          return;
        }
        auto parameter =
            model.add(Declaration::Kind::Parameter, scope, p.name, p.location);
        model.declarations[parameter.index].sort = p.sort.value_or("");
        model.declarations[owner.index].parameters.push_back(parameter);
      }
    };
    for (const auto &d : syntax.structs) {
      auto owner = id(d.name);
      parameters(owner, d.parameters);
      model.declarations[owner.index].checked = d.checked;
      for (const auto &constructor : d.constructors)
        model.declarations[owner.index].constructors.push_back(id(constructor));
    }
    for (const auto *header : functions) {
      const auto &d = *header;
      auto owner = id(d.name);
      parameters(owner, d.parameters);
      model.declarations[owner.index].generic = d.generic;
      model.declarations[owner.index].hasBody =
          bool(d.body) || entries.count(d.name);
      model.declarations[owner.index].bodyState =
          model.declarations[owner.index].hasBody
              ? Declaration::BodyState::Deferred
              : Declaration::BodyState::External;
    }
    if (original)
      for (const auto &p : original->protocols) {
        if (!p.generic)
          continue;
        auto owner = id(p.name);
        parameters(owner, p.staticParameters);
        model.declarations[owner.index].roles = p.roles;
        model.declarations[owner.index].naturalParameters = p.parameters;
        model.declarations[owner.index].generic = true;
        model.declarations[owner.index].hasBody = bool(p.body);
        model.declarations[owner.index].bodyState =
            p.body ? Declaration::BodyState::Deferred
                   : Declaration::BodyState::External;
      }
    for (const auto &d : syntax.protocols) {
      auto owner = id(d.name);
      model.declarations[owner.index].hasBody = bool(d.body);
      model.declarations[owner.index].bodyState =
          model.declarations[owner.index].hasBody
              ? Declaration::BodyState::Deferred
              : Declaration::BodyState::External;
      model.declarations[owner.index].roles = d.roles;
      model.declarations[owner.index].naturalParameters = d.parameters;
      ScopeId scope = model.declarations[owner.index].members;
      for (const auto &dependency : d.dependencies) {
        if (model.lookup(scope, dependency.name).valid()) {
          fail(dependency, "interactive-dependency",
               "duplicate dependency alias");
          return;
        }
        auto reference = model.add(Declaration::Kind::Dependency, scope,
                                   dependency.name, dependency.location);
        model.declarations[reference.index].target = id(dependency.protocol);
      }
    }
    auto requireKind = [&](const source::Node &node, DeclId target,
                           Declaration::Kind kind, StringRef description) {
      if (!target.valid() || model.declarations[target.index].kind != kind)
        fail(node, "source-declaration-kind",
             description + " requires a declaration of the expected kind");
    };
    for (const auto &p : syntax.protocols)
      for (const auto &d : p.dependencies)
        requireKind(d, id(d.protocol), Declaration::Kind::Protocol,
                    "dependency");
    for (const auto &d : syntax.instances)
      requireKind(d, id(d.protocol), Declaration::Kind::Protocol, "instance");
    for (const auto &d : syntax.entries)
      requireKind(d, id(d.instance), Declaration::Kind::Instance, "entry");
    for (const auto &d : syntax.configurations)
      model.declarations[id(d.name).index].target = id(d.base);
    for (const auto &d : syntax.instances)
      model.declarations[id(d.name).index].target = id(d.protocol);
    for (const auto &d : syntax.entries)
      model.declarations[id(d.name).index].target = id(d.instance);
  }
  std::optional<AggregateShape> shapeOf(TypeId type) {
    const auto t = model.types.at(type.index);
    if (t.kind == frontend::Type::Kind::Logical)
      return {};
    if (t.kind == frontend::Type::Kind::Product ||
        t.kind == frontend::Type::Kind::Array) {
      AggregateShape result;
      result.array = t.kind == frontend::Type::Kind::Array;
      result.product = !result.array;
      result.arity = result.array ? t.count : t.elements.size();
      if (result.array)
        result.arrayElement = t.elements.front();
      result.type = type;
      result.name = model.spelling(type);
      for (size_t i = 0; i < result.arity; ++i)
        if (auto nested = shapeOf(t.elements[result.array ? 0 : i])) {
          result.nested.emplace_back(std::to_string(i), *nested);
          for (const auto &[path, inner] : nested->nested)
            result.nested.emplace_back(std::to_string(i) + "." + path, inner);
        }
      for (const auto &leaf : model.layouts.at(type)) {
        result.paths.push_back(leaf.name);
        result.types.push_back(model.spelling(leaf.type));
      }
      return result;
    }
    const auto d = model.declarations.at(t.declaration.index);
    AggregateShape shape;
    shape.name = d.name;
    shape.declaration = d.id;
    shape.type = type;
    std::map<DeclId, DomainId> sub;
    for (auto [parameter, argument] : zip(d.parameters, t.arguments)) {
      sub.emplace(parameter, argument);
      shape.arguments.push_back(model.spelling(argument));
    }
    for (const auto &leaf : model.layouts.at(type)) {
      shape.paths.push_back(leaf.name);
      shape.types.push_back(model.spelling(leaf.type));
    }
    for (const auto &field : d.fields)
      if (auto nested = shapeOf(model.substitute(field.type, sub))) {
        shape.nested.emplace_back(field.name, *nested);
        for (const auto &[path, inner] : nested->nested)
          shape.nested.emplace_back(field.name + "." + path, inner);
      }
    return shape;
  }
  Signature projectSignature(DeclId id) {
    // The existing finite solver accepts leaf signatures. This projection is
    // derived from the retained typed signature each time, never authoritative.
    const auto d = model.declarations.at(id.index);
    Signature result;
    for (DeclId parameter : d.parameters) {
      const auto &p = model.declarations.at(parameter.index);
      result.parameters.push_back({p.name, p.sort});
    }
    for (const auto *ports : {&d.inputs, &d.outputs})
      for (const auto &port : *ports) {
        auto &shapes =
            ports == &d.inputs ? result.inputShapes : result.outputShapes;
        auto &types = ports == &d.inputs ? result.inputs : result.outputs;
        shapes.push_back(shapeOf(port.type));
        for (const auto &leaf : model.leaves(port))
          types.push_back(model.spelling(leaf.type));
      }
    for (const auto &r : d.requirements) {
      source::Requirement requirement;
      requirement.predicate = r.predicate;
      requirement.location = r.location;
      for (DomainId argument : r.arguments)
        requirement.arguments.push_back(model.spelling(argument));
      result.requirements.push_back(std::move(requirement));
    }
    return result;
  }
  void retainShape(AggregateShape &shape) {
    if (shape.array) {
      shape.type = model.array(shape.arrayElement, shape.arity);
      shape.name = model.spelling(shape.type);
    } else if (shape.product) {
      std::vector<TypeId> elements;
      for (size_t i = 0; i < shape.arity; ++i) {
        auto key = std::to_string(i);
        auto nested = llvm::find_if(
            shape.nested, [&](const auto &p) { return p.first == key; });
        if (nested != shape.nested.end())
          elements.push_back(nested->second.type);
        else {
          auto path = llvm::find(shape.paths, key);
          elements.push_back(model.logical(
              shape.types.at(path - shape.paths.begin()), activeScope));
        }
      }
      shape.type = model.product(elements);
      shape.name = model.spelling(shape.type);
    } else
      shape.type =
          model.record(shape.declaration, shape.arguments, activeScope);
    std::vector<Port> leaves;
    for (auto [path, type] : zip(shape.paths, shape.types))
      leaves.push_back({path, {}, model.logical(type, activeScope), {}});
    model.layouts[shape.type] = std::move(leaves);
  }
  TypeId sourceType(const syntax::Type &t,
                    const std::optional<AggregateShape> &shape,
                    const Sorts &scope, bool generic) {
    return shape ? shape->type
                 : model.logical(type(t, scope, generic), activeScope);
  }
  Requirement
  retainRequirement(const source::Requirement &r,
                    const std::map<std::string, std::string> &sub = {},
                    const Sorts &scope = {}) {
    Requirement result;
    result.predicate = r.predicate;
    result.location = r.location;
    for (const auto &term : r.arguments)
      result.arguments.push_back(
          model.internDomain(substitute(term, sub, scope), activeScope));
    return result;
  }
  void retainSignature(DeclId owner, const Signature &signature) {
    // Primitive signatures come from the installed operation owner. User
    // declarations retain authored aggregate ports separately below.
    auto scope = model.declarations[owner.index].members;
    for (const auto &p : signature.parameters) {
      auto parameter = model.lookup(scope, p.name);
      if (!parameter.valid()) {
        parameter = model.add(Declaration::Kind::Parameter, scope, p.name);
        model.declarations[owner.index].parameters.push_back(parameter);
      }
      model.declarations[parameter.index].sort = p.sort;
    }
  }
  void retainCall(const Call &call, StringRef owner, StringRef site,
                  const Signature &signature,
                  const std::map<std::string, std::string> &sub,
                  const source::Names &statics, const CallShapes &shapes,
                  const source::Names &, bool algorithm,
                  const generic::Operation *operation) {
    DeclId target;
    if (algorithm || !operation ||
        (!call.qualified && !model.declarations[id(owner).index].generic))
      target = id(call.callee);
    else {
      // Installed contracts inhabit their own scope, not the module namespace.
      if (operationScope.index == std::numeric_limits<uint32_t>::max())
        operationScope = model.addScope({}, {});
      target = model.lookup(operationScope, call.callee);
      if (!target.valid()) {
        target = model.add(Declaration::Kind::Operation, operationScope,
                           call.callee);
        retainSignature(target, signature);
        auto scope = model.declarations[target.index].members;
        for (const auto &t : signature.inputs)
          model.declarations[target.index].inputs.push_back(
              {{}, {}, model.logical(t, scope), {}});
        for (const auto &t : signature.outputs)
          model.declarations[target.index].outputs.push_back(
              {{}, {}, model.logical(t, scope), {}});
        auto previousScope = activeScope;
        activeScope = scope;
        for (const auto &r : signature.requirements)
          model.declarations[target.index].requirements.push_back(
              retainRequirement(r));
        activeScope = previousScope;
        model.declarations[target.index].signatureChecked = true;
      }
    }
    if (!target.valid()) {
      fail(call, "source-call-target", "call has no resolved declaration");
      return;
    }
    retainSignature(target, signature);
    if (!model.declarations[target.index].signatureChecked) {
      auto targetScope = model.declarations[target.index].members;
      for (const auto &t : signature.inputs)
        model.declarations[target.index].inputs.push_back(
            {{}, {}, model.logical(t, targetScope), {}});
      for (const auto &t : signature.outputs)
        model.declarations[target.index].outputs.push_back(
            {{}, {}, model.logical(t, targetScope), {}});
      auto previousScope = activeScope;
      activeScope = targetScope;
      for (const auto &r : signature.requirements)
        model.declarations[target.index].requirements.push_back(
            retainRequirement(r));
      activeScope = previousScope;
      model.declarations[target.index].signatureChecked = true;
    }
    ResolvedUse use;
    use.owner = id(owner);
    use.target = target;
    use.scope = activeScope;
    use.location = call.location;
    use.site = site.str();
    use.role = call.role.value_or("");
    use.writtenArguments = bool(call.staticArguments);
    auto parameterScope = model.declarations[target.index].members;
    for (auto [parameter, argument] : zip(signature.parameters, statics))
      use.bindings.push_back({model.lookup(parameterScope, parameter.name),
                              model.internDomain(argument, activeScope)});
    size_t flat = 0;
    for (auto [name, shape] : zip(call.outputs, shapes.results)) {
      TypeId type;
      if (shape) {
        type = shape->type;
        flat += shape->types.size();
      } else
        type = model.logical(substituteType(signature.outputs[flat++], sub, {}),
                             activeScope);
      use.results.push_back({name, use.role, type, call.location});
    }
    for (const auto &r : signature.requirements)
      use.requirements.push_back(retainRequirement(r, sub));
    model.uses.push_back(std::move(use));
  }
  void templates() {
    if (!original)
      return;
    for (const auto &p : original->protocols) {
      if (!p.generic || !good())
        continue;
      auto owner = id(p.name);
      activeScope = model.declarations[owner.index].members;
      Sorts scope;
      source::GenericFunction contract;
      contract.name = p.name;
      contract.location = p.location;
      for (const auto &parameter : p.staticParameters) {
        std::string sort = parameter.sort.value_or("");
        for (const auto &bound : parameter.bounds) {
          auto candidate = boundSort(bound, parameter);
          if (!sort.empty() && sort != candidate)
            fail(parameter, "source-bound-sort",
                 "bounds require different domain sorts");
          sort = candidate;
          source::Requirement r;
          r.location = parameter.location;
          r.predicate = bound;
          r.arguments = {parameter.name};
          contract.requirements.push_back(std::move(r));
        }
        if (sort != "Field" && sort != "Group" && sort != "Commitment" &&
            sort != "Transcript" && sort != "Codec")
          fail(parameter, "generic-declared-sort", "unknown domain sort");
        scope.emplace(parameter.name, sort);
        model.declarations[model.lookup(activeScope, parameter.name).index]
            .sort = sort;
        contract.parameters.push_back({parameter.name, sort});
      }
      if (!good())
        return;
      std::vector<std::string> origins(contract.requirements.size());
      for (const auto &r : p.requirements) {
        std::vector<std::string> stack;
        if (!expandRequirement(r, contract.requirements, origins, stack))
          return;
      }
      checkRequirements(contract, scope, origins);
      if (!good())
        return;
      for (const auto &r : contract.requirements)
        model.declarations[owner.index].requirements.push_back(
            retainRequirement(r));
      for (const auto &port : p.arguments) {
        auto shape = aggregateType(port.type, scope, false);
        auto type = sourceType(port.type, shape, scope, false);
        model.declarations[owner.index].inputs.push_back(
            {port.name, port.role, type, port.type.location});
      }
      for (const auto &port : p.results) {
        auto shape = aggregateType(port.type, scope, false);
        auto type = sourceType(port.type, shape, scope, false);
        model.declarations[owner.index].outputs.push_back(
            {port.name, port.role, type, port.type.location});
        if (!p.body && shape && model.containsChecked(type))
          fail(p, "source-checked-external",
               "bodiless protocol returns a checked aggregate without a "
               "constructor");
      }
      for (const auto &dependency : p.dependencies) {
        auto target = id(dependency.protocol);
        if (!target.valid() || model.declarations[target.index].kind !=
                                   Declaration::Kind::Protocol) {
          fail(dependency, "source-call-target",
               "unresolved protocol dependency");
          return;
        }
        if (model.lookup(activeScope, dependency.name).valid()) {
          fail(dependency, "interactive-dependency",
               "duplicate dependency alias");
          return;
        }
        auto alias = model.add(Declaration::Kind::Dependency, activeScope,
                               dependency.name, dependency.location);
        model.declarations[alias.index].target = target;
      }
      // Form all template signatures and references before checking any body.
      // Protocols.cpp then checks nominal ports, owned values and requirements;
      // resource and interaction admission remains with the common owner.
      auto body = [&](auto &&self, const syntax::Body &body) -> void {
        for (const auto &instruction : body) {
          if (const auto *call = std::get_if<Call>(&instruction.value)) {
            auto target = id(call->callee);
            if (!target.valid() || (model.declarations[target.index].kind !=
                                        Declaration::Kind::Function &&
                                    model.declarations[target.index].kind !=
                                        Declaration::Kind::Configuration))
              fail(*call, "source-call-target",
                   "protocol local requires a function or configuration "
                   "declaration");
            if (call->annotation)
              for (const auto &t : *call->annotation) {
                auto shape = aggregateType(t, scope, false);
                sourceType(t, shape, scope, false);
              }
          } else if (const auto *call =
                         std::get_if<syntax::Invocation>(&instruction.value)) {
            if (!model.lookup(activeScope, call->callee).valid())
              fail(instruction, "source-call-target",
                   "invoke requires a declared dependency alias");
          } else if (const auto *loop = std::get_if<Loop>(&instruction.value))
            self(self, loop->body);
        }
      };
      if (p.body)
        body(body, *p.body);
      model.declarations[owner.index].signatureChecked = good();
    }
  }
  void retainBody(model::DefinitionBody &definition,
                  const std::optional<source::Body> &body) {
    if (!body)
      return;
    auto resolved =
        resolveBody(model, definition.declaration, operationScope, *body);
    if (!resolved) {
      handleAllErrors(resolved.takeError(), [&](const SourceDiagnostic &d) {
        source::Node node;
        node.location = d.location;
        fail(node, d.code, d.message);
      });
      return;
    }
    definition.body = std::move(*resolved);
  }
  void retainPlans() {
    for (const auto &binding : module.bindings)
      if (!id(binding.name).valid())
        model.add(Declaration::Kind::Binding, {0}, binding.name,
                  binding.location);
    auto function = [&](const auto &f, std::optional<source::Body> body,
                        std::optional<source::LogicalOrigin> origin) {
      model::DefinitionBody plan;
      plan.declaration = id(f.name);
      retainBody(plan, body);
      plan.origin = std::move(origin);
      model.bodies.push_back(std::move(plan));
    };
    for (auto &placement : pendingPlacements) {
      model::DefinitionBody definition;
      definition.declaration = placement.definition;
      definition.emit = placement.emit;
      if (!model.declarations[placement.definition.index].generic)
        definition.origin = source::LogicalOrigin{
            model.declarations[placement.definition.index].name, {}};
      retainBody(definition, placement.body);
      model.bodies.push_back(std::move(definition));
    }
    for (auto &f : module.definitions)
      function(f, std::move(f.body), {});
    for (auto &f : module.functions)
      function(f, std::move(f.body), f.origin);
    for (auto &f : generated.functions) {
      // Retain source call queries for generated checked-library functions too.
      // Their bodies bypass authoring syntax, but not declaration resolution.
      if (f.body)
        source::walk(*f.body, [&](const source::Instruction &instruction) {
          std::string callee;
          source::Names names;
          if (const auto *call = instruction.get<source::AlgorithmCall>()) {
            callee = call->callee;
            names = call->outputs;
          } else if (const auto *call = instruction.get<source::Operation>()) {
            callee = call->callee;
            names = call->outputs;
          } else
            return;
          auto target = id(callee);
          if (!target.valid())
            return; // retainBody emits the owner diagnostic.
          ResolvedUse use;
          use.owner = id(f.name);
          use.target = target;
          use.scope = model.declarations[use.owner.index].members;
          use.location = instruction.location;
          use.site = instruction.site;
          const auto &outputs = model.declarations[target.index].outputs;
          for (unsigned i = 0; i < names.size() && i < outputs.size(); ++i)
            use.results.push_back(
                {names[i], {}, outputs[i].type, instruction.location});
          model.uses.push_back(std::move(use));
        });
      function(f, std::move(f.body), f.origin);
    }
    for (auto &p : module.protocols) {
      model::DefinitionBody plan;
      plan.declaration = id(p.name);
      retainBody(plan, p.body);
      plan.roles = std::move(p.roles);
      plan.naturalParameters = std::move(p.parameters);
      plan.dependencies = std::move(p.dependencies);
      model.bodies.push_back(std::move(plan));
    }
    module.functions.clear();
    module.definitions.clear();
    module.protocols.clear();
    model.metadata = std::move(module);
  }
  ScopeId operationScope;

  bool fail(const source::Node &node, StringRef c, const Twine &why) {
    if (code.empty()) {
      code = c.str();
      message = why.str();
      failure = node.location;
      model.diagnostics.push_back({code, message, failure});
    }
    return false;
  }
  bool good() const { return code.empty(); }
  std::string sortOf(StringRef term, const Sorts &scope, unsigned depth = 0) {
    if (depth > 64)
      return {};
    if (auto it = scope.find(term.str()); it != scope.end())
      return it->second;
    auto installed = protocol::installedIdentitySort(term);
    if (!installed.empty())
      return installed.str();
    auto [parent, member] = term.rsplit('.');
    if (parent.empty() || member.empty() || parent == term)
      return {};
    return protocol::associatedMemberSort(sortOf(parent, scope, depth + 1),
                                          member)
        .str();
  }
  std::string normalize(StringRef term, const Sorts &scope,
                        unsigned depth = 0) {
    if (depth > 64 || scope.count(term.str()) ||
        !protocol::installedIdentitySort(term).empty())
      return term.str();
    auto [parent, member] = term.rsplit('.');
    if (parent.empty() || member.empty() || parent == term)
      return term.str();
    auto p = normalize(parent, scope, depth + 1);
    auto associated = protocol::associatedIdentity(p, member);
    return associated.empty() ? p + "." + member.str() : associated.str();
  }
  bool genericTerm(StringRef term, const Sorts &scope, unsigned depth = 0) {
    if (scope.count(term.str()))
      return true;
    if (depth > 64)
      return false;
    auto [parent, member] = term.rsplit('.');
    return !parent.empty() && !member.empty() && parent != term &&
           genericTerm(parent, scope, depth + 1) &&
           !protocol::associatedMemberSort(sortOf(parent, scope), member)
                .empty();
  }
  void checkRequirements(const source::GenericFunction &function,
                         const Sorts &scope,
                         ArrayRef<std::string> origins = {}) {
    size_t position = 0;
    auto from = [&](size_t index) {
      return index < origins.size() && !origins[index].empty()
                 ? " (from bundle '" + origins[index] + "')"
                 : std::string{};
    };
    if (function.parameters.size() > 128 ||
        function.requirements.size() > 1024) {
      fail(function, "requirements-limit",
           "static contract exceeds the finite checker budget");
      return;
    }
    for (const auto &requirement : function.requirements) {
      const std::string origin = from(position++);
      generic::Signature signature;
      std::vector<unsigned> arguments;
      for (const auto &argument : requirement.arguments) {
        if (!genericTerm(argument, scope)) {
          fail(requirement, "source-generic-term",
               "generic requirements use parameters and their associated "
               "domains: '" +
                   argument + "'" + origin);
          return;
        }
        unsigned index = arguments.size();
        signature.scope.terms.push_back(
            {"argument" + std::to_string(index), {}});
        signature.scope.sorts.push_back(sortOf(argument, scope));
        arguments.push_back(index);
      }
      if (requirement.predicate == "=") {
        if (arguments.size() != 2) {
          fail(requirement, "generic-predicate-arity",
               "equality requires two nominal terms" + origin);
          return;
        }
        if (signature.scope.sorts[0] != signature.scope.sorts[1]) {
          fail(requirement, "generic-equality-sort",
               "equality requires terms of the same domain sort" + origin);
          return;
        }
      } else {
        signature.requirements.push_back(
            requirements::Predicate::holds(requirement.predicate, arguments));
        if (auto e = protocol::checkStaticVocabulary(signature)) {
          auto code = toString(std::move(e));
          fail(requirement, code,
               "invalid declared capability '" + requirement.predicate + "'" +
                   origin);
          return;
        }
      }
    }
  }
  unsigned projectionDepth(StringRef term, const Sorts &scope) {
    unsigned depth = 0;
    while (!scope.count(term.str()) &&
           protocol::installedIdentitySort(term).empty() && depth <= 64) {
      auto [parent, member] = term.rsplit('.');
      if (parent.empty() || member.empty() || parent == term)
        break;
      term = parent;
      ++depth;
    }
    return depth;
  }
  std::string domain(const syntax::Type &type, const Sorts &scope) {
    if (!type.arguments.empty()) {
      fail(type, "source-type",
           "expected a nominal domain, not a type application");
      return {};
    }
    if (!isDomainRoot(type.name, type.quoted)) {
      fail(type, "source-type-domain",
           "unknown domain root; use :: for associated members");
      return {};
    }
    std::string result = type.name;
    for (const auto &member : type.members)
      result += "." + member;
    return normalize(result, scope);
  }
  std::string type(const syntax::Type &t, const Sorts &scope,
                   bool generic = false) {
    if (t.name == "ResourceUnit" && t.members.empty()) {
      if (generic || t.arguments.size() != 1 || !t.arguments.front().quoted ||
          !t.arguments.front().arguments.empty() ||
          !t.arguments.front().members.empty()) {
        fail(t, "source-resource-unit",
             "ResourceUnit requires one closed nominal slot");
        return {};
      }
      auto spelling = "resource_unit:" + t.arguments.front().name;
      auto checked = protocol::parseBoundType(spelling, false);
      if (!checked) {
        consumeError(checked.takeError());
        fail(t, "source-resource-unit", "invalid logical resource slot");
        return {};
      }
      return model.spelling(model.logical(spelling, activeScope));
    }
    std::string kind, identity;
    if (!t.members.empty()) {
      if (t.members.back() != "Element" || !t.arguments.empty()) {
        fail(t, "source-type", "an element type must end in ::Element");
        return {};
      }
      syntax::Type root = t;
      root.members.pop_back();
      identity = domain(root, scope);
      auto sort = sortOf(identity, scope);
      if (sort == "Field")
        kind = "field";
      else if (sort == "Group")
        kind = "group";
      else {
        fail(t, "source-type-domain",
             "unknown or non-element domain '" + identity +
                 "'; ::Element requires a field or group domain");
        return {};
      }
    } else if (t.name == "Vector" || t.name == "Matrix") {
      if (t.arguments.size() != 1) {
        fail(t, "source-type-arity", "expected one element type");
        return {};
      }
      auto element = type(t.arguments[0], scope, generic);
      auto [base, value] = StringRef(element).split(':');
      if (base != "field" && !(t.name == "Vector" && base == "group")) {
        fail(t, "source-type",
             "expected a field element (or group element for Vector)");
        return {};
      }
      kind = t.name == "Matrix" ? "matrix"
             : base == "group"  ? "groups"
                                : "vector";
      identity = value.str();
    } else {
      for (const auto &spelling : typeSpellings)
        if (spelling.surface == t.name)
          kind = spelling.constructor.str();
      const auto defaultIdentity =
          usesProfile(t) ? profileIdentity(*syntax.profile, t.name)
                         : StringRef{};
      const bool profileShorthand =
          t.arguments.empty() && !defaultIdentity.empty();
      if (kind.empty() && profileShorthand)
        kind = t.name;
      if (kind.empty()) {
        fail(t, "source-type", "unknown logical type '" + t.name + "'");
        return {};
      }
      const generic::TypeConstructor *ctor = nullptr;
      for (const auto &candidate : protocol::boundTypeConstructors())
        if (candidate.name == kind)
          ctor = &candidate;
      if (!ctor || (t.arguments.size() != ctor->parameters.size() &&
                    !profileShorthand)) {
        fail(t, "source-type-arity", "wrong number of nominal type arguments");
        return {};
      }
      if (!t.arguments.empty()) {
        identity = domain(t.arguments[0], scope);
        if (sortOf(identity, scope) != ctor->parameters[0]) {
          fail(t, "source-type-domain",
               "domain has the wrong sort for " + t.name);
          return {};
        }
      } else if (profileShorthand)
        identity = defaultIdentity.str();
    }
    if (generic && !identity.empty() && !genericTerm(identity, scope)) {
      fail(t, "source-generic-term",
           "generic types use parameters and associated domains; configure the "
           "definition to select '" +
               identity + "'");
      return {};
    }
    return model.spelling(model.logical(
        identity.empty() ? kind : kind + ":" + identity, activeScope));
  }
  std::string boundSort(StringRef bound, const source::Node &node) {
    // Ask the installed vocabulary, rather than maintaining another trait
    // registry. Only the five nominal sorts are candidates, not backend
    // domains.
    std::string selected;
    for (StringRef sort :
         {"Field", "Group", "Commitment", "Transcript", "Codec"}) {
      generic::Signature signature;
      signature.scope.terms.push_back({"D", {}});
      signature.scope.sorts.push_back(sort.str());
      signature.requirements.push_back(
          requirements::Predicate::holds(bound.str(), {0}));
      if (auto e = protocol::checkStaticVocabulary(signature))
        consumeError(std::move(e));
      else {
        if (!selected.empty()) {
          fail(node, "source-bound-sort",
               "capability is valid at multiple sorts; use a domain sort and "
               "an explicit requires clause");
          return {};
        }
        selected = sort.str();
      }
    }
    if (!selected.empty())
      return selected;
    fail(node, "source-bound",
         bundles.count(bound.str())
             ? "a bundle is not a capability; use it in requires or where"
             : "expected an installed unary capability; use requires for "
               "other predicates");
    return {};
  }
  /// True when the installed vocabulary defines this predicate at any shape.
  bool installedPredicate(StringRef name) {
    generic::Signature signature;
    signature.requirements.push_back(
        requirements::Predicate::holds(name.str(), {}));
    auto e = protocol::checkStaticVocabulary(signature);
    return !e || toString(std::move(e)) != "generic-declared-predicate";
  }
  /// Replace the longest parameter prefix of a nominal term.
  static std::string bundleTerm(StringRef term,
                                const std::map<std::string, std::string> &sub,
                                bool *rooted) {
    const std::pair<const std::string, std::string> *best = nullptr;
    for (const auto &entry : sub) {
      StringRef parameter = entry.first;
      if ((term == parameter ||
           (term.starts_with(parameter) &&
            term.drop_front(parameter.size()).starts_with("."))) &&
          (!best || parameter.size() > best->first.size()))
        best = &entry;
    }
    *rooted = best;
    return best ? best->second + term.drop_front(best->first.size()).str()
                : term.str();
  }
  /// A bundle use is replaced in place by the bundle's requirements in their
  /// declared order, recursively. Nothing is sorted or deduplicated, so the
  /// stored list equals the one an author would have written by hand. The
  /// origin names the outermost bundle for diagnostics only.
  bool expandRequirement(const source::Requirement &requirement,
                         std::vector<source::Requirement> &out,
                         std::vector<std::string> &origins,
                         std::vector<std::string> &stack) {
    auto found = bundles.find(requirement.predicate);
    if (found == bundles.end()) {
      out.push_back(requirement);
      origins.push_back(stack.empty() ? std::string{} : stack.front());
      if (out.size() > 1024)
        return fail(requirement, "requirements-limit",
                    "static contract exceeds the finite checker budget");
      return true;
    }
    const Bundle &bundle = *found->second;
    if (requirement.arguments.size() != bundle.parameters.size())
      return fail(requirement, "source-bundle-arity",
                  "bundle '" + bundle.name + "' takes " +
                      Twine(bundle.parameters.size()) +
                      " arguments, received " +
                      Twine(requirement.arguments.size()));
    if (stack.size() >= 64 || llvm::is_contained(stack, bundle.name))
      return fail(requirement, "source-bundle-cycle",
                  "bundle '" + bundle.name +
                      "' reaches itself or nests deeper than 64");
    std::map<std::string, std::string> sub;
    for (auto [parameter, argument] :
         zip(bundle.parameters, requirement.arguments))
      sub.emplace(parameter, argument);
    stack.push_back(bundle.name);
    for (const auto &inner : bundle.requirements) {
      source::Requirement substituted = inner;
      substituted.location = requirement.location;
      bool rooted = false;
      for (auto &argument : substituted.arguments)
        argument = bundleTerm(argument, sub, &rooted);
      if (!expandRequirement(substituted, out, origins, stack))
        return false;
    }
    stack.pop_back();
    return true;
  }
  void declareBundles() {
    for (const auto &bundle : syntax.bundles) {
      if (!declare(bundle.name, bundle))
        return;
      if (bundle.name == "=" || installedPredicate(bundle.name)) {
        fail(bundle, "source-bundle-name",
             "'" + bundle.name + "' is an installed predicate");
        return;
      }
      std::map<std::string, std::string> identity;
      for (const auto &parameter : bundle.parameters)
        if (StringRef(parameter).contains('.') ||
            !protocol::installedIdentitySort(parameter).empty() ||
            !identity.emplace(parameter, parameter).second) {
          fail(bundle, "source-bundle-name",
               "bundle parameters must be unique undotted names distinct from "
               "installed identities");
          return;
        }
      for (const auto &requirement : bundle.requirements)
        for (const auto &argument : requirement.arguments) {
          bool rooted = false;
          bundleTerm(argument, identity, &rooted);
          if (!rooted) {
            fail(requirement, "source-bundle-term",
                 "bundle requirements use the bundle's parameters and their "
                 "associated domains: '" +
                     argument + "'");
            return;
          }
        }
      bundles.emplace(bundle.name, &bundle);
      for (const auto &terms : bundle.requirementTerms)
        for (const auto &term : terms)
          if (term.root.kind == Atom::Kind::String ||
              !isDomainRoot(term.root.value, false)) {
            fail(term.root, "source-bundle-term",
                 "bundle requirements use bound domains and explicit :: "
                 "members");
            return;
          }
    }
    // Expanding each bundle over its own parameters checks nested arity,
    // cycles and size where the bundle is declared, even if it is never used.
    for (const auto &bundle : syntax.bundles) {
      source::Requirement use;
      use.location = bundle.location;
      use.predicate = bundle.name;
      use.arguments = bundle.parameters;
      std::vector<source::Requirement> out;
      std::vector<std::string> origins, stack;
      if (!expandRequirement(use, out, origins, stack))
        return;
    }
  }
  bool declare(StringRef name, const source::Node &node) {
    if (!id(name).valid())
      model.add(Declaration::Kind::Binding, {0}, name, node.location);
    auto [previous, inserted] = declared.emplace(name.str(), node.location);
    if (inserted)
      return true;
    size_t offset = previous->second ? previous->second->offset : 0;
    const auto *file =
        previous->second ? model.resolution->input.file(previous->second->file)
                         : nullptr;
    auto prefix = (file ? file->text() : text).take_front(offset);
    size_t line = prefix.count('\n') + 1;
    size_t last = prefix.rfind('\n');
    size_t column = last == StringRef::npos ? offset + 1 : offset - last;
    return fail(node, "source-duplicate-symbol",
                "duplicate declaration '" + name +
                    "'; previous declaration at " +
                    (file ? file->filename() : filename) + ":" + Twine(line) +
                    ":" + Twine(column));
  }
  Sorts sorts(const std::vector<source::StaticParameter> &parameters) {
    Sorts result;
    for (const auto &p : parameters)
      result.emplace(p.name, p.sort);
    return result;
  }
  AggregateShape instantiate(const AggregateShape &shape,
                             const std::map<std::string, std::string> &sub,
                             const Sorts &scope) {
    AggregateShape result = shape;
    if (result.array) {
      if (auto element = shapeOf(result.arrayElement))
        result.arrayElement = instantiate(*element, sub, scope).type;
      else
        result.arrayElement = model.logical(
            substituteType(model.spelling(result.arrayElement), sub, scope),
            activeScope);
    }
    for (auto &argument : result.arguments)
      argument = substitute(argument, sub, scope);
    for (auto &type : result.types)
      type = substituteType(type, sub, scope);
    for (auto &[path, inner] : result.nested)
      inner = instantiate(inner, sub, scope);
    retainShape(result);
    return result;
  }
  bool resolveStruct(StringRef name, const source::Node &use, unsigned depth) {
    auto &info = structs.at(name.str());
    if (info.resolved)
      return true;
    if (info.resolving || depth > 64)
      return fail(use, "source-struct-cycle",
                  "struct '" + name +
                      "' contains itself or nests deeper "
                      "than 64");
    info.resolving = true;
    auto previousScope = activeScope;
    activeScope = model.declarations[id(name).index].members;
    auto restore = scope_exit([&] { activeScope = previousScope; });
    info.shape.declaration = id(name);
    const Struct &declaration = *info.declaration;
    info.shape.name = declaration.name;
    for (const auto &p : declaration.parameters) {
      // A struct records no capability assumption, so a bound would be
      // dropped. The functions that use the struct state their promises.
      if (!p.sort || !p.bounds.empty())
        return fail(p, "source-struct-bound",
                    "a struct declares domain sorts only; write '" + p.name +
                        ": domain Sort'");
      if (*p.sort != "Field" && *p.sort != "Group" && *p.sort != "Commitment" &&
          *p.sort != "Transcript" && *p.sort != "Codec")
        return fail(p, "generic-declared-sort", "unknown domain sort");
      if (!info.scope.emplace(p.name, *p.sort).second)
        return fail(p, "generic-duplicate-parameter",
                    "duplicate static parameter");
      info.parameters.push_back({p.name, *p.sort});
      model.declarations[model.lookup(activeScope, p.name).index].sort =
          *p.sort;
      info.shape.arguments.push_back(p.name);
    }
    if (declaration.fields.empty())
      return fail(declaration, "source-struct-field",
                  "a struct declares at least one field");
    const bool generic = !declaration.parameters.empty();
    std::set<std::string> seen;
    for (const auto &field : declaration.fields) {
      if (StringRef(field.name).contains('.') ||
          !seen.insert(field.name).second)
        return fail(field.type, "source-struct-field",
                    "field '" + field.name + "' is duplicated or contains '.'");
      if (auto nested =
              aggregateType(field.type, info.scope, generic, depth + 1)) {
        model.declarations[id(name).index].fields.push_back(
            {field.name, {}, nested->type, field.type.location});
        info.shape.nested.emplace_back(field.name, *nested);
        for (const auto &[path, inner] : nested->nested)
          info.shape.nested.emplace_back(field.name + "." + path, inner);
        for (auto [path, type] : zip(nested->paths, nested->types)) {
          info.shape.paths.push_back(field.name + "." + path);
          info.shape.types.push_back(type);
        }
      } else {
        if (!good())
          return false;
        info.shape.paths.push_back(field.name);
        info.shape.types.push_back(type(field.type, info.scope, generic));
        model.declarations[id(name).index].fields.push_back(
            {field.name,
             {},
             model.logical(info.shape.types.back(), activeScope),
             field.type.location});
        if (!good())
          return false;
      }
      if (info.shape.paths.size() > 4096)
        return fail(declaration, "source-struct-limit",
                    "a struct has at most 4096 leaf values");
    }
    retainShape(info.shape);
    model.declarations[id(name).index].signatureChecked = true;
    info.resolving = false;
    info.resolved = true;
    return true;
  }
  /// The shape of an authored struct type, or nothing for a logical type.
  /// After nothing, `good()` distinguishes a logical type from a refusal.
  std::optional<AggregateShape> aggregateType(const syntax::Type &t,
                                              const Sorts &scope, bool generic,
                                              unsigned depth = 0) {
    if (depth > 64) {
      fail(t, "source-type-depth", "aggregate type nesting exceeds 64");
      return {};
    }
    if (t.name == "Array" && !t.product && !t.quoted && t.members.empty()) {
      uint64_t count;
      if (t.arguments.size() != 2 || !t.arguments[1].natural ||
          !t.arguments[1].arguments.empty() ||
          !t.arguments[1].members.empty() ||
          StringRef(t.arguments[1].name).getAsInteger(10, count)) {
        fail(t, "source-array-count",
             "ordinary arrays require a concrete natural count");
        return {};
      }
      if (count > 4096) {
        fail(t, "source-array-limit", "an array has at most 4096 elements");
        return {};
      }
      auto elementShape =
          aggregateType(t.arguments.front(), scope, generic, depth + 1);
      auto element =
          sourceType(t.arguments.front(), elementShape, scope, generic);
      if (!good())
        return {};
      auto width = model.leaves({{}, {}, element, {}}).size();
      if ((width && count > 4096 / width) ||
          (elementShape && count > 4096 / (elementShape->nested.size() + 1))) {
        fail(t, "source-array-limit", "an array has at most 4096 leaf values");
        return {};
      }
      return shapeOf(model.array(element, count));
    }
    if (t.product) {
      std::vector<TypeId> elements;
      for (const auto &element : t.arguments) {
        auto aggregate = aggregateType(element, scope, generic, depth + 1);
        if (!good())
          return {};
        elements.push_back(sourceType(element, aggregate, scope, generic));
      }
      size_t leaves = 0;
      for (auto element : elements) {
        auto width = model.leaves({{}, {}, element, {}}).size();
        if (width > 4096 - leaves) {
          fail(t, "source-product-limit",
               "a product has at most 4096 leaf values");
          return {};
        }
        leaves += width;
      }
      return good() ? shapeOf(model.product(elements)) : std::nullopt;
    }
    auto found = t.members.empty() ? structs.find(t.name) : structs.end();
    if (found == structs.end() || !good())
      return {};
    if (!resolveStruct(t.name, t, depth))
      return {};
    const auto &info = found->second;
    if (t.arguments.size() != info.parameters.size()) {
      fail(t, "source-type-arity",
           "struct '" + t.name + "' takes " + Twine(info.parameters.size()) +
               " static arguments");
      return {};
    }
    std::map<std::string, std::string> sub;
    for (auto [parameter, argument] : zip(info.parameters, t.arguments)) {
      auto term = domain(argument, scope);
      if (!good())
        return {};
      if (generic && !genericTerm(term, scope)) {
        fail(argument, "source-generic-term",
             "generic types use parameters and associated domains; configure "
             "the definition to select '" +
                 term + "'");
        return {};
      }
      if (sortOf(term, scope) != parameter.sort) {
        fail(argument, "source-type-domain",
             "domain has the wrong sort for '" + parameter.name + "' of " +
                 t.name);
        return {};
      }
      sub.emplace(parameter.name, term);
    }
    return instantiate(info.shape, sub, scope);
  }
  bool sameAggregate(const AggregateShape &a, const AggregateShape &b,
                     const Sorts &scope,
                     ArrayRef<source::Requirement> assumptions,
                     const source::Node &node) {
    if (a.product != b.product || a.array != b.array || a.arity != b.arity ||
        a.declaration != b.declaration || a.nested.size() != b.nested.size() ||
        a.paths != b.paths || a.arguments.size() != b.arguments.size())
      return false;
    if (a.array) {
      auto left = shapeOf(a.arrayElement), right = shapeOf(b.arrayElement);
      if (bool(left) != bool(right) ||
          (left ? !sameAggregate(*left, *right, scope, assumptions, node)
                : !sameType(model.spelling(a.arrayElement),
                            model.spelling(b.arrayElement), scope, assumptions,
                            node)))
        return false;
    }
    for (auto [x, y] : zip(a.nested, b.nested))
      if (x.first != y.first ||
          (!StringRef(x.first).contains('.') &&
           !sameAggregate(x.second, y.second, scope, assumptions, node)))
        return false;
    for (auto [x, y] : zip(a.types, b.types))
      if (!sameType(x, y, scope, assumptions, node))
        return false;
    for (auto [x, y] : zip(a.arguments, b.arguments))
      if (!equivalent(x, y, scope, assumptions, node))
        return false;
    return true;
  }
  void arrayConstraints(
      const AggregateShape &expected, const AggregateShape &actual,
      std::vector<std::pair<std::string, std::string>> &constraints) {
    if (expected.array && actual.array) {
      auto left = shapeOf(expected.arrayElement),
           right = shapeOf(actual.arrayElement);
      if (left && right) {
        for (auto [x, y] : zip(left->types, right->types))
          constraints.emplace_back(x, y);
        arrayConstraints(*left, *right, constraints);
      } else if (!left && !right)
        constraints.emplace_back(model.spelling(expected.arrayElement),
                                 model.spelling(actual.arrayElement));
      return;
    }
    for (auto [left, right] : zip(expected.nested, actual.nested))
      if (left.first == right.first && !StringRef(left.first).contains('.'))
        arrayConstraints(left.second, right.second, constraints);
  }
  /// A use selects the one spelling whose symbol and operand constructors it
  /// has. The table names installed operations only, and each entry is checked
  /// against the installed signature, so it cannot say anything the
  /// operation's contract does not.
  std::optional<OperatorTarget> resolveOperator(const Expression &expression,
                                                ArrayRef<std::string> types) {
    for (const auto &spelling : operatorSpellings) {
      if (spelling.symbol != expression.name ||
          spelling.arity() != types.size())
        continue;
      bool matches = true;
      for (auto [index, type] : enumerate(types))
        matches &= StringRef(type).split(':').first == spelling.operands[index];
      if (!matches)
        continue;
      const generic::Operation *operation = nullptr;
      for (const auto &candidate : protocol::boundOperationContracts())
        if (candidate.name == spelling.operation)
          operation = &candidate;
      auto inputs = operation ? operationSignature(operation->signature).inputs
                              : source::Names{};
      bool installed = inputs.size() == types.size();
      for (unsigned k = 0; installed && k < inputs.size(); ++k)
        installed = StringRef(inputs[k]).split(':').first ==
                    spelling.operands[spelling.order[k]];
      if (!installed) {
        fail(expression, "source-operator-table",
             "operator '" + expression.name + "' names '" + spelling.operation +
                 "', whose installed signature differs");
        return {};
      }
      OperatorTarget target{spelling.operation.str(), true, {}};
      for (unsigned k = 0; k < types.size(); ++k)
        target.order.push_back(spelling.order[k]);
      return target;
    }
    std::string operands;
    for (const auto &type : types)
      operands += (operands.empty() ? "" : ", ") + type;
    fail(expression, "source-operator-unresolved",
         "'" + expression.name + "' is not an operator of (" + operands +
             "); call the operation by name");
    return {};
  }
  bool containsChecked(const AggregateShape &shape) {
    return model.containsChecked(shape.type);
  }

  /// A checked value must come from a constructor. It would arrive without
  /// one as the result of a function that has no body, or as a host-supplied
  /// input of an entry protocol; messages already refuse every struct.
  void checkCheckedStructs() {
    for (const auto &declaration : syntax.structs)
      for (const auto &name : declaration.constructors) {
        auto function = llvm::find_if(functions, [&](const auto *candidate) {
          return candidate->name == name;
        });
        bool returns = function != functions.end() &&
                       model.declarations[id(name).index].hasBody &&
                       llvm::any_of(getSignature(name).outputShapes,
                                    [&](const auto &shape) {
                                      return shape && shape->declaration ==
                                                          id(declaration.name);
                                    });
        if (!returns) {
          fail(declaration, "source-checked-constructor",
               "constructor '" + name + "' of " + declaration.name +
                   " must be a function in this module with a body and a " +
                   declaration.name + " result");
          return;
        }
      }
    for (const auto *function : functions)
      if (!model.declarations[id(function->name).index].hasBody)
        for (const auto &shape : getSignature(function->name).outputShapes)
          if (shape && containsChecked(*shape)) {
            fail(*function, "source-checked-external",
                 "'" + function->name + "' has no body, so its " + shape->name +
                     " result would not come from a constructor");
            return;
          }
    for (const auto &protocol : syntax.protocols)
      if (!protocol.body)
        for (const auto &shape : protocolSignature(protocol.name).outputShapes)
          if (shape && model.containsChecked(shape->type)) {
            fail(protocol, "source-checked-external",
                 "'" + protocol.name + "' has no body, so its " + shape->name +
                     " result would not come from a constructor");
            return;
          }
    for (const auto &entry : syntax.entries)
      for (const auto &instance : syntax.instances)
        if (instance.name == entry.instance)
          for (const auto &[name, shape] : structParameters[instance.protocol])
            if (containsChecked(shape)) {
              fail(entry, "source-checked-input",
                   "entry protocol '" + instance.protocol + "' receives '" +
                       name + "' from the host, so its " + shape.name +
                       " would not come from a constructor");
              return;
            }
  }
  void declareStructs() {
    for (const auto &declaration : syntax.structs) {
      if (!declare(declaration.name, declaration))
        return;
      // A struct named like a logical type would silently replace it.
      bool logical =
          declaration.name == "Vector" || declaration.name == "Matrix";
      for (const auto &spelling : typeSpellings)
        logical |= spelling.surface == declaration.name;
      if (logical) {
        fail(declaration, "source-struct-name",
             "'" + declaration.name + "' is a logical type");
        return;
      }
      structs[declaration.name].declaration = &declaration;
    }
    for (const auto &declaration : syntax.structs)
      if (!resolveStruct(declaration.name, declaration, 0))
        return;
  }
  /// Append one authored parameter or result as its flat leaves.
  template <typename Leaf>
  std::optional<AggregateShape> flattenType(const syntax::Type &t,
                                            const Sorts &scope, bool generic,
                                            Leaf leaf) {
    auto shape = aggregateType(t, scope, generic);
    if (shape)
      for (auto [path, type] : zip(shape->paths, shape->types))
        leaf("." + path, type);
    else if (good())
      leaf("", type(t, scope, generic));
    return shape;
  }
  void headers() {
    module.location = syntax.location;
    module.bindings = syntax.bindings;
    module.relations = syntax.relations;
    module.relationViews = syntax.relationViews;
    if (!syntax.imports.empty()) {
      fail(syntax.imports.front(), "relation-unresolved",
           "use the explicit dependency loader or protocol-resolve");
      return;
    }
    generated.relations = module.relations;
    generated.relationViews = module.relationViews;
    if (auto e = relation::materializeViews(generated)) {
      fail(syntax, "relation-admission", toString(std::move(e)));
      return;
    }
    // Linked bodies have already passed the abstract library checker. Preserve
    // exact carrier types and nested code; common admission independently
    // checks it.
    generated.functions.insert(generated.functions.end(),
                               linked.module.functions.begin(),
                               linked.module.functions.end());
    for (const auto &r : module.relations)
      declare(r.name, r);
    for (const auto &v : module.relationViews)
      declare(v.name, v);
    for (const auto &f : generated.functions) {
      declare(f.name, f);
      model.declarations[id(f.name).index].kind = Declaration::Kind::Function;
      algorithms.insert(f.name);
      Signature sig;
      sig.outputs = f.results;
      auto &declaration = model.declarations[id(f.name).index];
      for (const auto &p : f.arguments)
        declaration.inputs.push_back(
            {p.name,
             {},
             model.logical(p.type, declaration.members),
             f.location});
      for (const auto &t : f.results)
        declaration.outputs.push_back(
            {{}, {}, model.logical(t, declaration.members), f.location});
      declaration.signatureChecked = true;
      declaration.hasBody = bool(f.body);
      declaration.bodyState = f.body ? Declaration::BodyState::Checked
                                     : Declaration::BodyState::External;
      for (const auto &p : f.arguments)
        sig.inputs.push_back(p.type);
      signatures.emplace(id(f.name), std::move(sig));
    }
    module.bindings.insert(module.bindings.end(), generated.bindings.begin(),
                           generated.bindings.end());
    module.configurations = syntax.configurations;
    for (auto &configuration : module.configurations)
      for (auto &argument : configuration.arguments)
        argument.second = normalize(argument.second, {});
    module.instances = syntax.instances;
    module.entries = syntax.entries;
    for (const auto &b : module.bindings)
      declare(b.name, b);
    for (const auto &c : syntax.configurations) {
      declare(c.name, c);
      configurations.emplace(c.name, &c);
    }
    for (const auto &i : module.instances)
      declare(i.name, i);
    for (const auto &e : module.entries)
      declare(e.name, e);
    declareBundles();
    if (good())
      declareStructs();
    if (!good())
      return;
    for (const auto *header : functions) {
      const auto &f = *header;
      activeScope = model.declarations[id(f.name).index].members;
      declare(f.name, f);
      algorithms.insert(f.name);
      if (f.generic && usesProfile(f))
        fail(f, "source-profile-generic",
             "generic definitions require an explicit module; configure them "
             "to select concrete domains");
      if (!f.generic && !f.requirements.empty())
        fail(f, "source-function-contract",
             "where/requires clauses require an explicit generic function (use "
             "fn name<> for no parameters)");
      if (f.generic && f.origin)
        fail(f, "source-function-origin",
             "generic definitions do not accept an ordinary function origin");
      source::GenericFunction generic;
      generic.name = f.name;
      generic.location = f.location;
      Sorts scope;
      for (const auto &p : f.parameters) {
        std::string sort = p.sort.value_or("");
        for (const auto &bound : p.bounds) {
          auto candidate = boundSort(bound, p);
          if (!sort.empty() && candidate != sort)
            fail(p, "source-bound-sort",
                 "bounds require different domain sorts");
          sort = candidate;
          source::Requirement req;
          req.location = p.location;
          req.predicate = bound;
          req.arguments = {p.name};
          generic.requirements.push_back(std::move(req));
        }
        if (sort != "Field" && sort != "Group" && sort != "Commitment" &&
            sort != "Transcript" && sort != "Codec")
          fail(p, "generic-declared-sort", "unknown domain sort");
        if (!scope.emplace(p.name, sort).second)
          fail(p, "generic-duplicate-parameter", "duplicate static parameter");
        generic.parameters.push_back({p.name, sort});
        model.declarations[model.lookup(activeScope, p.name).index].sort = sort;
      }
      std::vector<std::string> origins(generic.requirements.size());
      for (const auto &terms : f.requirementTerms)
        for (const auto &term : terms)
          if (term.root.kind == Atom::Kind::String ||
              !isDomainRoot(term.root.value, false)) {
            fail(term.root, "source-generic-term",
                 "generic requirements use bound domains and explicit :: "
                 "members");
            return;
          }
      for (const auto &requirement : f.requirements) {
        std::vector<std::string> stack;
        if (!expandRequirement(requirement, generic.requirements, origins,
                               stack))
          return;
      }
      Signature sig;
      for (const auto &p : f.arguments) {
        auto shape = flattenType(
            p.type, scope, f.generic, [&](const Twine &path, StringRef type) {
              generic.arguments.push_back({(p.name + path).str(), type.str()});
            });
        if (shape)
          structParameters[f.name].emplace(p.name, *shape);
        model.declarations[id(f.name).index].inputs.push_back(
            {p.name,
             {},
             sourceType(p.type, shape, scope, f.generic),
             p.type.location});
        sig.inputShapes.push_back(std::move(shape));
      }
      for (const auto &r : f.results) {
        auto shape = flattenType(r, scope, f.generic,
                                 [&](const Twine &, StringRef type) {
                                   generic.results.push_back(type.str());
                                 });
        model.declarations[id(f.name).index].outputs.push_back(
            {{}, {}, sourceType(r, shape, scope, f.generic), r.location});
        sig.outputShapes.push_back(std::move(shape));
      }
      if (!good())
        return;
      if (f.generic)
        checkRequirements(generic, scope, origins);
      for (const auto &r : generic.requirements)
        model.declarations[id(f.name).index].requirements.push_back(
            retainRequirement(r));
      model.declarations[id(f.name).index].signatureChecked = good();
      sig.parameters = generic.parameters;
      sig.outputs = generic.results;
      sig.requirements = generic.requirements;
      for (const auto &p : generic.arguments)
        sig.inputs.push_back(p.type);
      signatures.emplace(id(f.name), std::move(sig));
      if (f.generic) {
        genericAlgorithms.insert(f.name);
        module.definitions.push_back(std::move(generic));
      } else {
        source::Function closed;
        closed.name = f.name;
        closed.location = f.location;
        closed.arguments = std::move(generic.arguments);
        closed.results = std::move(generic.results);
        closed.origin = f.origin;
        module.functions.push_back(std::move(closed));
      }
    }
    for (const auto &p : syntax.protocols) {
      activeScope = model.declarations[id(p.name).index].members;
      declare(p.name, p);
      source::Protocol out;
      out.location = p.location;
      out.name = p.name;
      out.roles = p.roles;
      out.parameters = p.parameters;
      out.dependencies = p.dependencies;
      Signature sig;
      for (const auto &a : p.arguments) {
        auto shape = flattenType(
            a.type, {}, false, [&](const Twine &path, StringRef type) {
              out.arguments.push_back(
                  {(a.name + path).str(), a.role, type.str()});
            });
        if (shape)
          structParameters[p.name].emplace(a.name, *shape);
        model.declarations[id(p.name).index].inputs.push_back(
            {a.name, a.role, sourceType(a.type, shape, {}, false),
             a.type.location});
        sig.inputShapes.push_back(std::move(shape));
      }
      for (const auto &r : p.results) {
        auto shape =
            flattenType(r.type, {}, false, [&](const Twine &, StringRef type) {
              out.results.push_back({r.role, type.str()});
            });
        model.declarations[id(p.name).index].outputs.push_back(
            {r.name, r.role, sourceType(r.type, shape, {}, false),
             r.type.location});
        sig.outputShapes.push_back(std::move(shape));
      }
      model.declarations[id(p.name).index].signatureChecked = good();
      for (const auto &a : out.arguments)
        sig.inputs.push_back(a.type);
      for (const auto &r : out.results)
        sig.outputs.push_back(r.type);
      module.protocols.push_back(std::move(out));
    }
    if (good())
      checkCheckedStructs();
  }
  std::string substitute(StringRef term,
                         const std::map<std::string, std::string> &sub,
                         const Sorts &scope, unsigned depth = 0) {
    if (auto it = sub.find(term.str()); it != sub.end())
      return it->second;
    if (depth > 64)
      return term.str();
    auto [parent, member] = term.rsplit('.');
    if (parent.empty() || member.empty() || parent == term)
      return term.str();
    auto changed = substitute(parent, sub, scope, depth + 1);
    return normalize(changed + "." + member.str(), scope);
  }
  std::string substituteType(StringRef t,
                             const std::map<std::string, std::string> &sub,
                             const Sorts &scope) {
    auto [kind, term] = t.split(':');
    return term.empty() ? t.str()
                        : kind.str() + ":" + substitute(term, sub, scope);
  }
  const Signature *configuration(StringRef name, const source::Node &node,
                                 unsigned depth = 0) {
    if (auto it = signatures.find(id(name)); it != signatures.end())
      return &it->second;
    auto record = configurations.find(name.str());
    if (record == configurations.end()) {
      fail(node, "generic-configuration-reference",
           "unknown configuration or definition");
      return nullptr;
    }
    if (depth > 64 || !resolving.insert(name.str()).second) {
      fail(*record->second, "generic-configuration-cycle",
           "cyclic or excessively deep configuration");
      return nullptr;
    }
    auto clearResolving = scope_exit([&] { resolving.erase(name.str()); });
    const auto &c = *record->second;
    auto base = configuration(c.base, c, depth + 1);
    if (!base)
      return nullptr;
    if (!genericAlgorithms.count(c.base)) {
      fail(c, "generic-configuration-reference",
           "configuration requires a generic definition");
      return nullptr;
    }
    std::map<std::string, std::string> sub;
    for (const auto &[key, value] : c.arguments) {
      auto p = llvm::find_if(base->parameters, [key = key](const auto &p) {
        return p.name == key;
      });
      if (p == base->parameters.end() ||
          !sub.emplace(key, normalize(value, {})).second) {
        fail(c, "generic-configuration-binding",
             "duplicate or unknown configuration parameter");
        return nullptr;
      }
      if (sortOf(value, {}) != p->sort) {
        fail(c, "generic-configuration-binding",
             "configuration argument has wrong domain sort");
        return nullptr;
      }
    }
    auto previousScope = activeScope;
    activeScope = model.declarations[id(name).index].members;
    auto restoreScope = scope_exit([&] { activeScope = previousScope; });
    Signature sig;
    for (const auto &p : base->parameters)
      if (!sub.count(p.name))
        sig.parameters.push_back(p);
    retainSignature(id(name), sig);
    for (const auto &t : base->inputs)
      sig.inputs.push_back(substituteType(t, sub, {}));
    for (const auto &t : base->outputs)
      sig.outputs.push_back(substituteType(t, sub, {}));
    for (const auto *shapes : {&base->inputShapes, &base->outputShapes})
      for (const auto &shape : *shapes)
        (shapes == &base->inputShapes ? sig.inputShapes : sig.outputShapes)
            .push_back(shape ? std::optional<AggregateShape>(
                                   instantiate(*shape, sub, {}))
                             : std::nullopt);
    for (const auto &req : base->requirements) {
      auto specialized = req;
      for (auto &argument : specialized.arguments)
        argument = substitute(argument, sub, {});
      sig.requirements.push_back(std::move(specialized));
    }
    retainSignature(id(name), sig);
    auto baseId = id(c.base);
    std::map<DeclId, DomainId> bindings;
    Instantiation instantiation;
    instantiation.definition = baseId;
    instantiation.emitted = id(name);
    instantiation.location = c.location;
    for (DeclId parameter : model.declarations[baseId.index].parameters) {
      const auto p = model.declarations[parameter.index];
      DomainId term;
      if (auto it = sub.find(p.name); it != sub.end()) {
        term = model.internDomain(it->second, activeScope);
        instantiation.bindings.push_back({parameter, term});
      } else
        term = model.internDomain(p.name, activeScope);
      bindings.emplace(parameter, term);
    }
    auto baseDeclaration = model.declarations[baseId.index];
    for (const auto *ports :
         {&baseDeclaration.inputs, &baseDeclaration.outputs})
      for (auto port : *ports) {
        port.type = model.substitute(port.type, bindings);
        (ports == &baseDeclaration.inputs
             ? model.declarations[id(name).index].inputs
             : model.declarations[id(name).index].outputs)
            .push_back(port);
      }
    for (const auto &r : sig.requirements)
      model.declarations[id(name).index].requirements.push_back(
          retainRequirement(r));
    model.declarations[id(name).index].signatureChecked = true;
    model.instantiations.push_back(std::move(instantiation));
    genericAlgorithms.insert(name.str());
    algorithms.insert(name.str());
    return &signatures.emplace(id(name), std::move(sig)).first->second;
  }
  Signature operationSignature(const generic::Signature &signature) {
    Signature out;
    source::Names terms;
    for (auto [i, term] : enumerate(signature.scope.terms)) {
      if (term.parent)
        terms.push_back(terms[*term.parent] + "." + term.name);
      else if (auto fixed = signature.scope.constants.find(i);
               fixed != signature.scope.constants.end())
        terms.push_back(fixed->second);
      else {
        terms.push_back(term.name);
        out.parameters.push_back({term.name, signature.scope.sorts[i]});
      }
    }
    auto convert = [&](const generic::Type &t) {
      return t.arguments.empty() ? t.constructor
                                 : t.constructor + ":" + terms[t.arguments[0]];
    };
    for (const auto &t : signature.inputs)
      out.inputs.push_back(convert(t));
    for (const auto &t : signature.outputs)
      out.outputs.push_back(convert(t));
    for (const auto &req : signature.requirements) {
      source::Requirement requirement;
      requirement.predicate =
          req.kind == requirements::Predicate::Kind::Equal ? "=" : req.relation;
      for (unsigned argument : req.arguments)
        requirement.arguments.push_back(terms[argument]);
      out.requirements.push_back(std::move(requirement));
    }
    return out;
  }
  bool equivalent(StringRef a, StringRef b, const Sorts &scope,
                  ArrayRef<source::Requirement> assumptions,
                  const source::Node &node) {
    if (a == b)
      return true;
    auto left = normalize(a, scope), right = normalize(b, scope);
    if (left == right)
      return true;
    // Reuse the finite congruence engine. Do not infer capabilities or reverse
    // a projection from equality of its outputs.
    std::vector<requirements::Term> terms;
    std::map<std::string, unsigned> indices;
    std::function<std::optional<unsigned>(StringRef, unsigned)> intern =
        [&](StringRef term, unsigned depth) -> std::optional<unsigned> {
      if (auto it = indices.find(term.str()); it != indices.end())
        return it->second;
      if (terms.size() >= 128 || depth > 64) {
        fail(node, "source-inference-limit",
             "nominal equality scope exceeds its budget");
        return {};
      }
      std::optional<unsigned> parent;
      std::string name = term.str();
      if (!scope.count(name) && protocol::installedIdentitySort(term).empty()) {
        auto pair = term.rsplit('.');
        if (!pair.first.empty() && !pair.second.empty() && pair.first != term) {
          parent = intern(pair.first, depth + 1);
          if (!parent)
            return {};
          name = pair.second.str();
        }
      }
      if (terms.size() >= 128) {
        fail(node, "source-inference-limit",
             "nominal equality scope exceeds its budget");
        return {};
      }
      unsigned i = terms.size();
      terms.push_back({name, parent});
      indices.emplace(term.str(), i);
      return i;
    };
    std::vector<requirements::Predicate> premises;
    for (const auto &r : assumptions) {
      if (r.predicate != "=" || r.arguments.size() != 2)
        continue;
      auto x = intern(normalize(r.arguments[0], scope), 0),
           y = intern(normalize(r.arguments[1], scope), 0);
      if (!x || !y)
        return false;
      if (sortOf(r.arguments[0], scope) != sortOf(r.arguments[1], scope))
        return false;
      premises.push_back(requirements::Predicate::equal(*x, *y));
    }
    auto x = intern(left, 0), y = intern(right, 0);
    if (!x || !y)
      return false;
    auto proof = requirements::derive(terms, premises, {},
                                      {requirements::Predicate::equal(*x, *y)});
    if (!proof) {
      fail(node, "source-inference-limit", toString(proof.takeError()));
      return false;
    }
    return proof->goals[0].has_value();
  }
  bool sameType(StringRef a, StringRef b, const Sorts &scope,
                ArrayRef<source::Requirement> assumptions,
                const source::Node &node) {
    auto [ak, at] = a.split(':');
    auto [bk, bt] = b.split(':');
    return ak == bk && equivalent(at, bt, scope, assumptions, node);
  }
  /// Record written static arguments. Inference fills the rest.
  bool writtenStatics(ArrayRef<source::StaticParameter> parameters,
                      const std::optional<source::Names> &written,
                      ArrayRef<syntax::StaticTerm> terms, const Sorts &scope,
                      bool generic, const source::Node &node,
                      std::map<std::string, std::string> &sub) {
    if (!written)
      return true;
    if (written->size() != parameters.size())
      return fail(node, "generic-static-arity",
                  "supply every static argument, or omit the complete list "
                  "for inference");
    size_t position = 0;
    for (auto [p, t] : zip(parameters, *written)) {
      if (position < terms.size() &&
          !isDomainRoot(terms[position].root.value,
                        terms[position].root.kind == Atom::Kind::String))
        return fail(node, "source-static-sort",
                    "unknown domain root; use :: for associated members");
      ++position;
      if (generic && !genericTerm(t, scope))
        return fail(node, "source-generic-term",
                    "generic call arguments must be parameters or associated "
                    "domains: '" +
                        t + "'");
      if (sortOf(t, scope) != p.sort)
        return fail(node, "source-static-sort",
                    "argument '" + t + "' for '" + p.name + "' requires sort " +
                        p.sort);
      sub.emplace(p.name, normalize(t, scope));
    }
    return true;
  }
  /// Determine every static parameter from (declared, actual) type pairs and
  /// check each pair under the result. Calls and struct constructions share
  /// this rule, so neither can infer what the other would refuse.
  bool solveStatics(ArrayRef<source::StaticParameter> parameters,
                    ArrayRef<std::string> resultTypes, bool written,
                    ArrayRef<std::pair<std::string, std::string>> constraints,
                    const Sorts &scope,
                    ArrayRef<source::Requirement> assumptions,
                    const source::Node &node, StringRef callee,
                    std::map<std::string, std::string> &sub,
                    source::Names &statics) {
    for (const auto &[pattern, actual] : constraints) {
      auto [pk, pt] = StringRef(pattern).split(':');
      auto [ak, at] = StringRef(actual).split(':');
      if (pk != ak) {
        fail(
            node, "source-type-mismatch",
            "operand or result annotation has a different logical constructor");
        return false;
      }
      auto p = llvm::find_if(parameters,
                             [pt = pt](const auto &p) { return p.name == pt; });
      if (p == parameters.end())
        continue;
      auto [it, inserted] = sub.emplace(p->name, normalize(at, scope));
      if (!inserted && !equivalent(it->second, at, scope, assumptions, node)) {
        fail(node, "source-static-conflict",
             "callee '" + callee + "': incompatible constraints for '" +
                 p->name + "': '" + it->second + "' and '" + at + "'");
        return false;
      }
      // Explicit arguments retain their authored spelling. Inference selects
      // one stable representative among equal constraint-supplied terms.
      auto candidate = normalize(at, scope);
      if (!written &&
          std::make_pair(projectionDepth(candidate, scope), candidate) <
              std::make_pair(projectionDepth(it->second, scope), it->second))
        it->second = std::move(candidate);
    }
    for (const auto &p : parameters) {
      auto it = sub.find(p.name);
      if (it == sub.end()) {
        std::string arguments;
        for (const auto &parameter : parameters) {
          if (!arguments.empty())
            arguments += ", ";
          arguments += parameter.name;
        }
        bool inResult = llvm::any_of(resultTypes, [&](const auto &type) {
          return StringRef(type).split(':').second == p.name;
        });
        fail(node, "source-static-unresolved",
             "cannot determine '" + p.name + "' for '" + callee +
                 "'; supply ::<" + arguments + ">" +
                 (inResult ? " or annotate this call's result type"
                           : " explicitly"));
        return false;
      }
      if (sortOf(it->second, scope) != p.sort) {
        fail(node, "source-static-sort",
             "static argument has the wrong nominal sort");
        return false;
      }
      statics.push_back(it->second);
    }
    for (const auto &[pattern, actual] : constraints)
      if (!sameType(substituteType(pattern, sub, scope), actual, scope,
                    assumptions, node)) {
        fail(node, "source-type-mismatch",
             "operand or result annotation disagrees with the resolved "
             "signature");
        return false;
      }
    return good();
  }
  std::optional<source::Instruction::Value>
  call(const Call &call, const Sorts &scope,
       ArrayRef<source::Requirement> assumptions, Values &values, bool generic,
       StringRef owner, StringRef site, CallShapes &shapes) {
    if (call.role) {
      fail(call, "source-local-control",
           "participant-owned calls belong in protocol bodies");
      return {};
    }
    Signature signature;
    bool algorithm = !call.qualified && algorithms.count(call.callee);
    const generic::Operation *operation = nullptr;
    for (const auto &op : protocol::boundOperationContracts())
      if (op.name == call.callee)
        operation = &op;
    if (call.qualified && !operation) {
      fail(call, usesProfile(call) ? "binding-contract" : "source-call-target",
           "qualified calls name installed operation contracts; use the exact "
           "declaration name for helpers");
      return {};
    }
    if (algorithm) {
      if (generic && !genericAlgorithms.count(call.callee)) {
        fail(call, "generic-call-target",
             "generic bodies require a generic helper or configuration");
        return {};
      }
      signature = getSignature(call.callee);
      if (!call.attributes.empty()) {
        fail(call, "algorithm-call-syntax",
             "algorithm calls do not accept operation attributes");
        return {};
      }
    } else if (operation && (generic || call.qualified)) {
      signature = operationSignature(operation->signature);
    } else if (!generic) {
      auto it = llvm::find_if(module.bindings, [&](const auto &b) {
        return b.name == call.callee;
      });
      if (it == module.bindings.end()) {
        fail(call, "binding-reference",
             "unknown bound operation or helper '" + call.callee + "'");
        return {};
      }
      auto resolved = protocol::resolveBinding(it->application, false);
      if (!resolved) {
        fail(call, "source-call-binding", toString(resolved.takeError()));
        return {};
      }
      for (const auto &t : resolved->inputs)
        signature.inputs.push_back(t.spelling());
      for (const auto &t : resolved->outputs)
        signature.outputs.push_back(t.spelling());
    } else {
      fail(call, generic ? "generic-operation" : "source-call-target",
           "unknown callable '" + call.callee + "'");
      return {};
    }
    // Operands and results are counted as authored: a struct is one of each,
    // whatever its number of leaves.
    const Shapes inputShapes =
        authored(signature.inputShapes, signature.inputs.size());
    Shapes outputShapes =
        authored(signature.outputShapes, signature.outputs.size());
    if (outputShapes.size() == 1 && outputShapes.front() &&
        outputShapes.front()->product &&
        (call.destructure ||
         (call.outputs.empty() && outputShapes.front()->arity == 0))) {
      const auto elements =
          model.types.at(outputShapes.front()->type.index).elements;
      outputShapes.clear();
      for (auto element : elements)
        outputShapes.push_back(shapeOf(element));
    } else if (!call.destructure && call.outputs.size() == 1 &&
               outputShapes.size() != 1) {
      std::vector<TypeId> elements;
      size_t next = 0;
      for (const auto &shape : outputShapes) {
        elements.push_back(
            shape ? shape->type
                  : model.logical(signature.outputs.at(next), activeScope));
        next += shape ? shape->paths.size() : 1;
      }
      outputShapes = {*shapeOf(model.product(elements))};
    }
    if (shapes.operands.size() != inputShapes.size()) {
      fail(call, "source-call-arity",
           "callee '" + call.callee + "' expects " + Twine(inputShapes.size()) +
               " inputs, received " + Twine(shapes.operands.size()));
      return {};
    }
    for (auto [index, pair] : enumerate(zip(shapes.operands, inputShapes))) {
      const auto &[operand, declared] = pair;
      if (bool(operand) != bool(declared)) {
        fail(call, "source-struct-value",
             "input " + Twine(index + 1) + " of '" + call.callee + "' is " +
                 (declared ? "the struct " + declared->name
                           : std::string("a single value")) +
                 ", but the operand is " +
                 (operand ? "the struct " + operand->name
                          : std::string("a single value")));
        return {};
      }
      if (operand && !sameAggregateStructure(*operand, *declared)) {
        fail(call, "source-struct-mismatch",
             "input " + Twine(index + 1) + " of '" + call.callee +
                 "' declares " + declared->name + ", received " +
                 operand->name);
        return {};
      }
    }
    if (call.outputs.size() != outputShapes.size()) {
      fail(call, "source-call-arity",
           "callee '" + call.callee + "' produces " +
               Twine(outputShapes.size()) + " results, bound " +
               Twine(call.outputs.size()) +
               "; bare calls require zero results");
      return {};
    }
    source::Names outputs;
    for (auto [name, shape] : zip(call.outputs, outputShapes)) {
      if (!shape)
        outputs.push_back(name);
      else
        for (const auto &path : shape->paths)
          outputs.push_back(name + "." + path);
    }
    std::map<std::string, std::string> sub;
    if (!writtenStatics(signature.parameters, call.staticArguments,
                        call.staticTerms, scope, generic, call, sub))
      return {};
    std::vector<std::pair<std::string, std::string>> constraints;
    for (auto [name, expected] : zip(call.inputs, signature.inputs)) {
      auto it = values.find(name);
      if (it == values.end()) {
        fail(call, "source-value-reference",
             "unknown input value '" + name + "'");
        return {};
      }
      constraints.emplace_back(expected, it->second);
    }
    for (auto [operand, declared] : zip(shapes.operands, inputShapes))
      if (operand && declared)
        arrayConstraints(*declared, *operand, constraints);
    Shapes annotationShapes(outputShapes.size());
    auto annotations = call.annotation;
    if (annotations && call.destructure && annotations->size() == 1 &&
        annotations->front().product)
      annotations = std::vector<syntax::Type>(annotations->front().arguments);
    if (annotations) {
      if (annotations->size() != outputShapes.size()) {
        fail(call, "source-annotation-arity",
             "annotation must cover every result");
        return {};
      }
      size_t flat = 0;
      for (auto [index, pair] : enumerate(zip(*annotations, outputShapes))) {
        const auto &[annotation, shape] = pair;
        if (!shape) {
          constraints.emplace_back(signature.outputs[flat++],
                                   type(annotation, scope, generic));
          continue;
        }
        auto annotated = aggregateType(annotation, scope, generic);
        if (!annotated || !sameAggregateStructure(*annotated, *shape)) {
          if (good())
            fail(annotation, "source-struct-mismatch",
                 "this result is the struct " + shape->name);
          return {};
        }
        annotationShapes[index] = annotated;
        arrayConstraints(*shape, *annotated, constraints);
        for (const auto &leaf : annotated->types)
          constraints.emplace_back(signature.outputs[flat++], leaf);
      }
    }
    source::Names statics;
    if (!solveStatics(signature.parameters, signature.outputs,
                      bool(call.staticArguments), constraints, scope,
                      assumptions, call, call.callee, sub, statics))
      return {};
    for (auto [operand, declared] : zip(shapes.operands, inputShapes))
      if (operand && !sameAggregate(instantiate(*declared, sub, scope),
                                    *operand, scope, assumptions, call)) {
        fail(call, "source-struct-mismatch",
             "the operand's static arguments differ from those '" +
                 call.callee + "' declares for " + declared->name);
        return {};
      }
    for (auto [shape, annotation] : zip(outputShapes, annotationShapes))
      if (annotation && !sameAggregate(instantiate(*shape, sub, scope),
                                       *annotation, scope, assumptions, call)) {
        if (good())
          fail(call, "source-annotation-type",
               "result annotation differs from its instantiated source type");
        return {};
      }
    shapes.results.clear();
    for (const auto &shape : outputShapes)
      shapes.results.push_back(
          shape ? std::optional<AggregateShape>(instantiate(*shape, sub, scope))
                : std::nullopt);
    shapes.outputs = outputs;
    if (!good())
      return {};
    retainCall(call, owner, site, signature, sub, statics, shapes, outputs,
               algorithm, operation);
    for (auto [name, result] : zip(outputs, signature.outputs))
      if (!values.emplace(name, substituteType(result, sub, scope)).second) {
        fail(call, "source-value-duplicate",
             "values are single assignment; duplicate '" + name + "'");
        return {};
      }
    if (algorithm)
      return source::AlgorithmCall{call.callee, call.inputs, outputs,
                                   std::move(statics)};
    std::string target = call.callee;
    if (!generic && call.qualified && operation) {
      std::string implementation;
      if (usesProfile(call)) {
        source::OperationBinding requested;
        requested.application.contract = call.callee;
        requested.application.arguments = statics;
        auto selected = protocol::defaultImplementation(requested.application);
        if (!selected) {
          fail(call, "source-profile", toString(selected.takeError()));
          return {};
        }
        implementation = *selected;
      }
      auto binding = llvm::find_if(module.bindings, [&](const auto &b) {
        return b.application.contract == call.callee &&
               b.application.arguments == statics &&
               b.application.implementation == implementation;
      });
      if (binding == module.bindings.end()) {
        target = usesProfile(call)
                     ? call.callee
                     : "__binding_" + std::to_string(module.bindings.size());
        while (declared.count(target) ||
               llvm::any_of(module.bindings,
                            [&](const auto &b) { return b.name == target; }))
          target += "_";
        source::OperationBinding generated;
        generated.location = call.location;
        generated.name = target;
        generated.application.contract = call.callee;
        generated.application.arguments = statics;
        generated.application.implementation = implementation;
        module.bindings.push_back(std::move(generated));
      } else
        target = binding->name;
      statics.clear();
    }
    return source::Operation{target, std::move(statics), call.attributes,
                             call.inputs, outputs};
  }
  /// Flat names of authored protocol-level names. At this level a struct
  source::Body localBody(const Body &input, const Sorts &scope,
                         ArrayRef<source::Requirement> assumptions,
                         Values values, bool generic, StringRef owner,
                         TypeId *inferred = nullptr) {
    LocalCallbacks callbacks;
    callbacks.inferResult = inferred != nullptr;
    callbacks.returned = [&](const source::Names &values,
                             const std::optional<AggregateShape> &shape,
                             const LocalTypes &types) {
      if (inferred)
        *inferred = shape
                        ? shape->type
                        : model.logical(types.at(values.front()), activeScope);
    };
    callbacks.argumentOrder =
        [&](const Call &call) -> std::optional<std::vector<unsigned>> {
      std::vector<unsigned> order;
      auto target = id(call.callee);
      if (call.qualified || !target.valid() ||
          (model.declarations[target.index].kind !=
               Declaration::Kind::Function &&
           model.declarations[target.index].kind !=
               Declaration::Kind::Configuration)) {
        if (call.argumentNames.empty())
          return order;
        fail(call, "source-argument-name",
             "named arguments require a declared function signature");
        return {};
      }
      const auto &ports = model.declarations[target.index].inputs;
      library::Signature signature;
      signature.inputs.resize(ports.size());
      for (const auto &port : ports)
        signature.inputLabels.push_back(port.name);
      auto binding = library::bindArguments(signature, call.inputs.size(),
                                            call.argumentNames);
      if (!binding) {
        fail(call,
             call.argumentNames.empty() ? "source-call-arity"
                                        : "source-argument-name",
             toString(binding.takeError()));
        return {};
      }
      order.resize(binding->size());
      for (unsigned written = 0; written < binding->size(); ++written)
        order[(*binding)[written]] = written;
      return order;
    };
    // Reconstruct source expectations from resolved ports. Unknown generic
    // domains remain absent until a rigid operand/result or explicit actual
    // determines them; this never searches for a component or inverts a type.
    std::function<std::optional<syntax::Type>(
        TypeId, const std::map<DeclId, DomainId> &, const std::set<DeclId> &)>
        expectation;
    expectation =
        [&](TypeId id, const std::map<DeclId, DomainId> &sub,
            const std::set<DeclId> &unknown) -> std::optional<syntax::Type> {
      const auto t = model.types.at(model.substitute(id, sub).index);
      syntax::Type result;
      if (t.kind == frontend::Type::Kind::Array) {
        auto element = expectation(t.elements.front(), sub, unknown);
        if (!element)
          return {};
        result.name = "Array";
        syntax::Type count;
        count.natural = true;
        count.name = std::to_string(t.count);
        result.arguments = {std::move(*element), std::move(count)};
        return result;
      }
      result.product = t.kind == frontend::Type::Kind::Product;
      result.name = t.kind == frontend::Type::Kind::Record
                        ? model.declarations.at(t.declaration.index).name
                        : t.constructor;
      if (result.product) {
        for (auto element : t.elements) {
          auto expected = expectation(element, sub, unknown);
          if (!expected)
            return {};
          result.arguments.push_back(*expected);
        }
      } else
        for (auto argument : t.arguments) {
          auto root = argument;
          while (model.domains.at(root.index).kind == Domain::Kind::Projection)
            root = model.domains.at(root.index).parent;
          if (unknown.count(model.domains.at(root.index).parameter))
            return {};
          syntax::Type domain;
          domain.name = model.spelling(root);
          domain.quoted =
              model.domains.at(root.index).kind == Domain::Kind::Identity;
          for (auto member = argument; member != root;
               member = model.domains.at(member.index).parent)
            domain.members.insert(domain.members.begin(),
                                  model.domains.at(member.index).name);
          result.arguments.push_back(std::move(domain));
        }
      if (t.kind == frontend::Type::Kind::Logical) {
        for (const auto &spelling : typeSpellings)
          if (spelling.constructor == t.constructor)
            result.name = spelling.surface.str();
        if ((t.constructor == "field" || t.constructor == "group") &&
            result.arguments.size() == 1) {
          auto element = std::move(result.arguments.front());
          result = std::move(element);
          result.members.push_back("Element");
        } else if ((t.constructor == "vector" || t.constructor == "groups" ||
                    t.constructor == "matrix") &&
                   result.arguments.size() == 1) {
          result.name = t.constructor == "matrix" ? "Matrix" : "Vector";
          result.arguments.front().members.push_back("Element");
        } else if (t.constructor == "resource_unit")
          result.name = "ResourceUnit";
      }
      return result;
    };
    callbacks.argumentTypes = [&](const Call &call, const LocalTypes &types,
                                  const Shapes &shapes) {
      std::vector<std::optional<syntax::Type>> result;
      auto target = id(call.callee);
      if (call.qualified || !target.valid())
        return result;
      const auto d = model.declarations.at(target.index);
      if (d.kind != Declaration::Kind::Function &&
          d.kind != Declaration::Kind::Configuration)
        return result;
      std::map<DeclId, DomainId> sub;
      std::set<DeclId> unknown(d.parameters.begin(), d.parameters.end());
      if (call.staticArguments &&
          call.staticArguments->size() == d.parameters.size())
        for (auto [parameter, argument] :
             zip(d.parameters, *call.staticArguments)) {
          sub.emplace(parameter, model.internDomain(argument, activeScope));
          unknown.erase(parameter);
        }
      auto order = callbacks.argumentOrder(call);
      if (!order)
        return result;
      auto constrain = [&](TypeId pattern, StringRef actual) {
        const auto &t = model.types.at(pattern.index);
        auto [constructor, domain] = actual.split(':');
        if (t.kind != frontend::Type::Kind::Logical ||
            t.constructor != constructor || t.arguments.size() != 1 ||
            domain.empty())
          return;
        const auto &p = model.domains.at(t.arguments.front().index);
        if (p.kind == Domain::Kind::Parameter && unknown.count(p.parameter)) {
          sub.emplace(p.parameter, model.internDomain(domain, activeScope));
          unknown.erase(p.parameter);
        }
      };
      auto constrainShape = [&](auto &&self, TypeId pattern,
                                TypeId actual) -> void {
        const auto x = model.types.at(pattern.index),
                   y = model.types.at(actual.index);
        if (x.kind != y.kind || x.constructor != y.constructor ||
            x.declaration != y.declaration || x.count != y.count ||
            x.arguments.size() != y.arguments.size() ||
            x.elements.size() != y.elements.size())
          return;
        for (auto [formal, value] : zip(x.arguments, y.arguments)) {
          const auto &parameter = model.domains.at(formal.index);
          if (parameter.kind == Domain::Kind::Parameter &&
              unknown.count(parameter.parameter)) {
            sub.emplace(parameter.parameter, value);
            unknown.erase(parameter.parameter);
          }
        }
        for (auto [formal, value] : zip(x.elements, y.elements))
          self(self, formal, value);
      };
      for (unsigned i = 0; i < d.inputs.size() && i < order->size(); ++i) {
        auto found = types.find(call.inputs[(*order)[i]]);
        if (found != types.end())
          constrain(d.inputs[i].type, found->second);
        if ((*order)[i] < shapes.size() && shapes[(*order)[i]])
          constrainShape(constrainShape, d.inputs[i].type,
                         shapes[(*order)[i]]->type);
      }
      if (call.annotation && call.annotation->size() == 1 &&
          d.outputs.size() == 1) {
        auto shape = aggregateType(call.annotation->front(), scope, generic);
        if (shape)
          constrainShape(constrainShape, d.outputs.front().type, shape->type);
        else if (good())
          constrain(d.outputs.front().type,
                    type(call.annotation->front(), scope, generic));
      }
      for (const auto &port : d.inputs)
        result.push_back(expectation(port.type, sub, unknown));
      return result;
    };
    callbacks.fieldTypes =
        [&](const Expression &expression,
            const std::optional<std::vector<syntax::Type>> &annotation) {
          std::vector<std::optional<syntax::Type>> result;
          auto target = id(expression.name);
          if (!target.valid() || model.declarations[target.index].kind !=
                                     Declaration::Kind::Record)
            return result;
          const auto d = model.declarations.at(target.index);
          std::map<DeclId, DomainId> sub;
          std::set<DeclId> unknown(d.parameters.begin(), d.parameters.end());
          if (annotation && annotation->size() == 1) {
            auto expected = aggregateType(annotation->front(), scope, generic);
            if (expected && expected->declaration == target)
              for (auto [parameter, argument] :
                   zip(d.parameters,
                       model.types.at(expected->type.index).arguments)) {
                sub.emplace(parameter, argument);
                unknown.erase(parameter);
              }
          }
          if (expression.staticArguments &&
              expression.staticArguments->size() == d.parameters.size())
            for (auto [parameter, argument] :
                 zip(d.parameters, *expression.staticArguments)) {
              sub[parameter] = model.internDomain(argument, activeScope);
              unknown.erase(parameter);
            }
          for (const auto &name : expression.fields) {
            auto field = llvm::find_if(
                d.fields, [&](const auto &f) { return f.name == name; });
            result.push_back(field == d.fields.end()
                                 ? std::nullopt
                                 : expectation(field->type, sub, unknown));
          }
          return result;
        };
    const auto &signature = getSignature(owner.str());
    callbacks.results =
        authored(signature.outputShapes, signature.outputs.size());
    callbacks.resultTypes = signature.outputs;
    const auto &ownerDeclaration = model.declarations.at(id(owner).index);
    if (ownerDeclaration.outputs.size() == 1)
      callbacks.resultAnnotation =
          expectation(ownerDeclaration.outputs.front().type, {}, {});
    callbacks.construct = [&](const Expression &expression,
                              ArrayRef<ConstructedField> fields,
                              const LocalTypes &types) {
      return construct(expression, fields, types, scope, assumptions, generic,
                       owner);
    };
    callbacks.sameAggregate = [&](const AggregateShape &a,
                                  const AggregateShape &b,
                                  const source::Node &node) {
      return sameAggregate(a, b, scope, assumptions, node);
    };
    callbacks.resolveOperator = [&](const Expression &expression,
                                    ArrayRef<std::string> types) {
      return resolveOperator(expression, types);
    };
    callbacks.call = [&](const Call &callSyntax, LocalTypes &types,
                         StringRef site, CallShapes &shapes) {
      auto adjusted = callSyntax;
      if (auto it = profileCalls.find({owner.str(), adjusted.callee});
          !adjusted.qualified && it != profileCalls.end()) {
        adjusted.callee = it->second;
        adjusted.qualified = false;
      }
      return call(adjusted, scope, assumptions, types, generic, owner, site,
                  shapes);
    };
    callbacks.product = [&](ArrayRef<ConstructedField> fields,
                            const LocalTypes &types) {
      std::vector<TypeId> elements;
      for (const auto &field : fields)
        elements.push_back(
            field.shape
                ? field.shape->type
                : model.logical(types.at(field.values.front()), activeScope));
      return *shapeOf(model.product(elements));
    };
    callbacks.aggregate = [&](const syntax::Type &spelling) {
      return aggregateType(spelling, scope, generic);
    };
    callbacks.type = [&](const syntax::Type &spelling) {
      return type(spelling, scope, generic);
    };
    callbacks.same = [&](StringRef a, StringRef b, const source::Node &node) {
      return sameType(a, b, scope, assumptions, node);
    };
    callbacks.fail = [&](const source::Node &node, StringRef code,
                         const Twine &message) { fail(node, code, message); };
    callbacks.good = [&] { return good(); };
    LocalSymbols symbols(model, id(owner), activeScope);
    return elaborateLocal(input, std::move(values),
                          structParameters[owner.str()], callbacks, symbols);
  }
  bool constructionAllowed(const StructInfo &info,
                           const source::Node &expression, StringRef owner) {
    const auto &declared = info.shape;
    // A checked struct is built only where its checks are written. Everywhere
    // else its values can be passed, returned and read, but not made.
    if (info.declaration->checked &&
        !llvm::is_contained(info.declaration->constructors, owner.str())) {
      fail(expression, "source-checked-construction",
           "'" + declared.name + "' is constructed only in " +
               llvm::join(info.declaration->constructors, ", ") +
               "; call a constructor to obtain a value");
      return false;
    }
    return true;
  }
  void checkEntry(const LibraryEntry &entry, source::Function &formed) {
    const auto owner = id(formed.name);
    std::vector<source::Names> paths;
    for (const auto &port : model.declarations[owner.index].outputs) {
      source::Names names;
      for (const auto &leaf : model.leaves(port))
        names.push_back(leaf.name);
      paths.push_back(std::move(names));
    }
    // Resolve the expected target from the checked link judgment, independently
    // of the generated call being checked. Equal port types alone do not make
    // a different linked implementation the correct target for this alias.
    const auto &links = model.libraries->links;
    auto link = llvm::find_if(links, [&](const auto &binding) {
      return binding.first == formed.name;
    });
    auto target = llvm::find_if(linked.module.functions, [&](const auto &f) {
      return link != links.end() && f.name == link->second.entry();
    });
    if (target == linked.module.functions.end()) {
      fail(entry.header, "source-library-entry-layout",
           "linked entry has no internal target");
      return;
    }
    if (auto error = checkLibraryEntry(entry, formed, paths, *target)) {
      handleAllErrors(std::move(error), [&](const Refusal &e) {
        fail(entry.header, e.code, e.detail);
      });
      return;
    }
    // The old source wrapper reconstructed result records. Retain its
    // constructor-authority judgment, including nested records; an empty array
    // creates no element. Formation has already checked its element type.
    std::function<bool(TypeId)> constructible = [&](TypeId id) {
      const auto t = model.types.at(id.index);
      if (t.kind == frontend::Type::Kind::Array)
        return t.count == 0 || constructible(t.elements.front());
      if (t.kind == frontend::Type::Kind::Product)
        return llvm::all_of(t.elements, constructible);
      if (t.kind != frontend::Type::Kind::Record)
        return true;
      const auto declaration = model.declarations[t.declaration.index];
      std::map<DeclId, DomainId> substitution;
      for (auto [parameter, argument] :
           zip(declaration.parameters, t.arguments))
        substitution.emplace(parameter, argument);
      for (const auto &field : declaration.fields)
        if (!constructible(model.substitute(field.type, substitution)))
          return false;
      const auto &name = declaration.name;
      return constructionAllowed(structs.at(name), entry.header, formed.name);
    };
    for (const auto &port : model.declarations[owner.index].outputs)
      if (!constructible(port.type))
        return;
    // A forwarding call is useful provenance. Invented local bindings and
    // record-construction expressions are not authored source events.
    ResolvedUse use;
    const auto *call =
        entry.forwarding.body->front().get<source::AlgorithmCall>();
    use.owner = owner;
    use.target = id(target->name);
    use.scope = activeScope;
    use.location = entry.header.location;
    use.site = "invoke";
    for (size_t i = 0; i < call->outputs.size(); ++i)
      use.results.push_back({call->outputs[i],
                             {},
                             model.logical(target->results[i], activeScope),
                             entry.header.location});
    model.uses.push_back(std::move(use));
    formed.body = entry.forwarding.body;
  }
  /// A construction arranges existing values and emits nothing. Its static
  /// arguments follow the rule used for calls, with the struct's leaf types in
  /// the place of a callee's parameters.
  std::optional<AggregateShape>
  construct(const Expression &expression, ArrayRef<ConstructedField> fields,
            const LocalTypes &types, const Sorts &scope,
            ArrayRef<source::Requirement> assumptions, bool generic,
            StringRef owner) {
    auto found = structs.find(expression.name);
    if (found == structs.end()) {
      fail(expression, "source-type",
           "unknown struct '" + expression.name + "'");
      return {};
    }
    const auto &info = found->second;
    const AggregateShape &declared = info.shape;
    if (!constructionAllowed(info, expression, owner))
      return {};
    std::map<std::string, const ConstructedField *> written;
    for (const auto &field : fields)
      if (!written.emplace(field.name, &field).second ||
          llvm::none_of(info.declaration->fields, [&](const auto &candidate) {
            return candidate.name == field.name;
          })) {
        fail(expression, "source-struct-field",
             "field '" + field.name + "' is repeated or is not a field of " +
                 declared.name);
        return {};
      }
    std::vector<std::pair<std::string, std::string>> constraints;
    size_t leaf = 0;
    for (const auto &field : info.declaration->fields) {
      auto it = written.find(field.name);
      if (it == written.end()) {
        fail(expression, "source-struct-field",
             "construction of " + declared.name + " omits field '" +
                 field.name + "'");
        return {};
      }
      const AggregateShape *nested = nullptr;
      for (const auto &[path, inner] : declared.nested)
        if (path == field.name)
          nested = &inner;
      const ConstructedField &value = *it->second;
      if (bool(nested) != bool(value.shape)) {
        fail(expression, "source-struct-value",
             "field '" + field.name + "' of " + declared.name + " is " +
                 (nested ? "a struct" : "a single value"));
        return {};
      }
      if (nested && !sameAggregateStructure(*nested, *value.shape)) {
        fail(expression, "source-struct-mismatch",
             "field '" + field.name + "' declares " + nested->name +
                 ", received " + value.shape->name);
        return {};
      }
      if (value.values.size() != (nested ? nested->paths.size() : 1)) {
        fail(expression, "source-struct-mismatch",
             "field layout differs from its declared type");
        return {};
      }
      for (const auto &name : value.values) {
        auto type = types.find(name);
        if (type == types.end()) {
          fail(expression, "source-value-reference",
               "unknown input value '" + name + "'");
          return {};
        }
        constraints.emplace_back(declared.types[leaf++], type->second);
      }
    }
    std::map<std::string, std::string> sub;
    source::Names statics;
    if (!writtenStatics(info.parameters, expression.staticArguments,
                        expression.staticTerms, scope, generic, expression,
                        sub) ||
        !solveStatics(info.parameters, {}, bool(expression.staticArguments),
                      constraints, scope, assumptions, expression,
                      declared.name, sub, statics))
      return {};
    auto result = instantiate(declared, sub, scope);
    for (const auto &field : fields) {
      auto expected = llvm::find_if(result.nested, [&](const auto &entry) {
        return entry.first == field.name;
      });
      if (expected != result.nested.end() &&
          !sameAggregate(expected->second, *field.shape, scope, assumptions,
                         expression)) {
        if (good())
          fail(expression, "source-struct-mismatch",
               "field differs from its instantiated source type");
        return {};
      }
    }

    ResolvedUse use;
    use.kind = ResolvedUse::Kind::Construct;
    use.owner = id(owner);
    use.target = result.declaration;
    use.scope = activeScope;
    use.location = expression.location;
    use.writtenArguments = bool(expression.staticArguments);
    for (auto [parameter, term] :
         zip(model.declarations[result.declaration.index].parameters, statics))
      use.bindings.push_back(
          {parameter, model.internDomain(term, activeScope)});
    use.results.push_back({{}, {}, result.type, expression.location});
    model.uses.push_back(std::move(use));
    return result;
  }
  void profiles() {
    if (!syntax.profile)
      return;
    for (auto &f : module.functions) {
      auto sf = llvm::find_if(syntax.functions, [&](const auto &candidate) {
        return candidate.name == f.name;
      });
      if (sf == syntax.functions.end() || !sf->body || !usesProfile(*sf))
        continue;
      f.body = source::Body{};
      std::set<std::string> operations;
      auto collect = [&](const source::Node &node, StringRef callee,
                         bool qualified) {
        // Qualified calls infer their actual domains through the ordinary
        // resolver. Only the profile's unqualified shorthand needs defaults.
        if (qualified || algorithms.count(callee.str()) ||
            !operations.insert(callee.str()).second)
          return;
        source::Instruction op;
        op.site = callee.str();
        op.location = node.location;
        op.value = source::Operation{callee.str(), {}, {}, {}, {}};
        f.body->push_back(std::move(op));
      };
      auto expression = [&](auto &&self, const Expression &expr) -> void {
        for (const auto &operand : expr.operands)
          self(self, operand);
        if (expr.kind == Expression::Kind::Call)
          collect(expr, expr.name, expr.qualified);
      };
      auto visit = [&](auto &&self, const Body &body) -> void {
        for (const auto &ins : body) {
          if (auto *call = std::get_if<Call>(&ins.value);
              call && !call->isOperator)
            collect(*call, call->callee, call->qualified);
          else if (auto *binding = std::get_if<Binding>(&ins.value))
            expression(expression, binding->expression);
          else if (auto *exit = std::get_if<Exit>(&ins.value))
            expression(expression, exit->expression);
          else if (auto *branch = std::get_if<Conditional>(&ins.value)) {
            expression(expression, branch->condition);
            self(self, branch->thenBody);
            self(self, branch->elseBody);
          } else if (auto *loop = std::get_if<For>(&ins.value)) {
            expression(expression, loop->lower);
            expression(expression, loop->upper);
            self(self, loop->body);
          }
        }
      };
      visit(visit, *sf->body);
    }
    // Only the installed convenience profiles have defaults to expand; any
    // other module header names nothing the carrier could hold.
    if (!knownProfile(*syntax.profile)) {
      fail(syntax, "source-profile",
           "unknown convenience profile '" + *syntax.profile + "'");
      return;
    }
    elaborateProfile(module, *syntax.profile);
    for (const auto &binding : module.bindings)
      if (!id(binding.name).valid())
        model.add(Declaration::Kind::Binding, {0}, binding.name,
                  binding.location);
    for (auto &f : module.functions) {
      if (f.body)
        for (const auto &ins : *f.body)
          if (!profileCalls
                   .emplace(std::make_pair(f.name, ins.site),
                            ins.get<source::Operation>()->callee)
                   .second)
            fail(ins, "interactive-site", "duplicate operation site");
      f.body.reset();
    }
  }

  std::optional<CheckedPlacement> placement(DeclId protocolOwner,
                                            const syntax::Placement &placement,
                                            const source::Instruction &site,
                                            ArrayRef<Port> available,
                                            bool emit) {
    const auto parent = model.declarations[protocolOwner.index];
    std::string name = "__local_" + std::to_string(parent.name.size()) + "_" +
                       parent.name + "_" + site.site;
    while (id(name).valid())
      name += "_";
    auto helper =
        model.add(Declaration::Kind::Function, {0}, name, site.location);
    auto previous = activeScope;
    activeScope = model.declarations[helper.index].members;
    auto restore = scope_exit([&] { activeScope = previous; });
    std::map<DeclId, DomainId> substitution;
    Sorts scope;
    Signature signature;
    for (auto parameter : parent.parameters) {
      const auto p = model.declarations[parameter.index];
      auto fresh = model.add(Declaration::Kind::Parameter, activeScope, p.name,
                             p.location);
      model.declarations[fresh.index].sort = p.sort;
      model.declarations[helper.index].parameters.push_back(fresh);
      substitution.emplace(parameter, model.internDomain(p.name, activeScope));
      scope.emplace(p.name, p.sort);
      signature.parameters.push_back({p.name, p.sort});
    }
    bool generic = !parent.parameters.empty();
    model.declarations[helper.index].generic = generic;
    std::vector<source::Requirement> assumptions;
    for (auto requirement : parent.requirements) {
      source::Requirement leaf;
      leaf.predicate = requirement.predicate;
      for (auto &arg : requirement.arguments) {
        arg = model.substitute(arg, substitution);
        leaf.arguments.push_back(model.spelling(arg));
      }
      model.declarations[helper.index].requirements.push_back(requirement);
      assumptions.push_back(std::move(leaf));
    }
    signature.requirements = assumptions;
    Values values;
    for (auto port : available) {
      port.type = model.substitute(port.type, substitution);
      if (auto shape = shapeOf(port.type))
        structParameters[name].emplace(port.name, *shape);
      for (const auto &leaf : model.leaves(port))
        values.emplace(leaf.name, model.spelling(leaf.type));
    }
    signatures.emplace(helper, signature);
    algorithms.insert(name);
    if (generic)
      genericAlgorithms.insert(name);
    TypeId result;
    auto body = localBody(placement.body, scope, assumptions, values, generic,
                          name, &result);
    if (!good())
      return {};
    if (!result.valid() || body.empty() || !body.back().get<source::Return>()) {
      fail(site, "source-local-result",
           "a placement block requires a final value or explicit return");
      return {};
    }
    // Closure conversion captures only used leaves. An unrelated affine value
    // available at the same role must not become an implicit operand.
    source::Names free;
    std::set<std::string> seen;
    auto use = [&](ArrayRef<std::string> names) {
      for (const auto &n : names)
        if (values.count(n) && seen.insert(n).second)
          free.push_back(n);
    };
    for (const auto &ins : body) {
      if (auto *op = ins.get<source::Operation>())
        use(op->inputs);
      else if (auto *call = ins.get<source::AlgorithmCall>())
        use(call->inputs);
      else if (auto *branch = ins.get<source::Conditional>()) {
        use({branch->condition});
        use(branch->captures);
      } else if (auto *loop = ins.get<source::For>()) {
        use({loop->lower, loop->upper});
        for (const auto &entry : loop->carried)
          use({entry.second});
        use(loop->captures);
      } else if (auto *ret = ins.get<source::Return>())
        use(ret->values);
    }
    CheckedPlacement checked;
    checked.function = helper;
    for (const auto &name : free) {
      checked.captures.push_back(name);
      model.declarations[helper.index].inputs.push_back(
          {name,
           {},
           model.logical(values.at(name), activeScope),
           site.location});
    }
    auto &d = model.declarations[helper.index];
    d.outputs.push_back({{}, {}, result, site.location});
    d.hasBody = true;
    d.signatureChecked = true;
    d.bodyState = Declaration::BodyState::Checked;
    signatures[helper] = projectSignature(helper);
    // The generic template is checked and retained; only selected closed
    // protocol bodies contribute closure functions to the emitted module.
    pendingPlacements.push_back({helper, std::move(body), emit});
    return checked;
  }
  struct PendingPlacement {
    DeclId definition;
    source::Body body;
    bool emit;
  };
  std::vector<PendingPlacement> pendingPlacements;

public:
  Checker(model::Module &model, const Module &syntax, const Module *original,
          const LibraryEmission &linked)
      : model(model), syntax(syntax), original(original), text(model.text),
        filename(model.filename), linked(linked) {
    assert(model.resolution && "semantic checking requires resolved input");
    for (const auto &f : syntax.functions)
      functions.push_back(&f);
    for (const auto &entry : linked.entries) {
      functions.push_back(&entry.header);
      entries.emplace(entry.header.name, &entry);
    }
  }
  bool run() {
    predeclare();
    if (!good())
      return false;
    headers();
    if (good())
      profiles();
    if (good())
      for (const auto &c : syntax.configurations) {
        configuration(c.name, c);
        if (!good())
          break;
      }
    if (good())
      templates();
    if (good() && original)
      for (const auto &p : original->protocols) {
        if (!p.generic)
          continue;
        auto owner = id(p.name);
        activeScope = model.declarations[owner.index].members;
        Sorts scope;
        for (auto parameter : model.declarations[owner.index].parameters) {
          const auto &d = model.declarations[parameter.index];
          scope.emplace(d.name, d.sort);
        }
        auto resolve = [&](const syntax::Type &t) {
          auto shape = aggregateType(t, scope, false);
          auto result = sourceType(t, shape, scope, false);
          return good() ? result : TypeId{};
        };
        auto local = [&](const syntax::Placement &block,
                         const source::Instruction &site, ArrayRef<Port> ports,
                         bool emit) {
          return placement(owner, block, site, ports, emit);
        };
        if (!checkProtocolBody(model, p, resolve, local))
          return false;
      }
    size_t gi = 0, fi = 0;
    for (const auto *header : functions) {
      const auto &f = *header;
      if (!good())
        break;
      activeScope = model.declarations[id(f.name).index].members;
      Values values;
      const auto &args = f.generic ? module.definitions[gi].arguments
                                   : module.functions[fi].arguments;
      for (const auto &p : args)
        if (!values.emplace(p.name, p.type).second)
          fail(f, "source-value-duplicate", "duplicate function argument");
      if (f.generic) {
        auto &out = module.definitions[gi++];
        if (!f.body) {
          fail(f, "source-generic-body", "generic definitions require a body");
          break;
        }
        out.body = localBody(*f.body, sorts(out.parameters), out.requirements,
                             values, true, f.name);
      } else {
        auto &out = module.functions[fi++];
        if (auto entry = entries.find(f.name); entry != entries.end())
          checkEntry(*entry->second, out);
        else if (f.body)
          out.body = localBody(*f.body, {}, {}, values, false, f.name);
      }
    }
    if (good())
      for (auto [p, out] : zip(syntax.protocols, module.protocols)) {
        activeScope = model.declarations[id(p.name).index].members;
        auto resolve = [&](const syntax::Type &t) {
          auto shape = aggregateType(t, {}, false);
          auto result = sourceType(t, shape, {}, false);
          return good() ? result : TypeId{};
        };
        auto owner = id(p.name);
        auto local = [&](const syntax::Placement &block,
                         const source::Instruction &site, ArrayRef<Port> ports,
                         bool emit) {
          return placement(owner, block, site, ports, emit);
        };
        if (!checkProtocolBody(model, p, resolve, local, &out))
          return false;
      }
    if (!good())
      return false;
    retainPlans();
    for (const auto &plan : model.bodies)
      if (plan.body)
        model.declarations[plan.declaration.index].bodyState =
            Declaration::BodyState::Checked;
    return good();
  }
};
} // namespace
bool check(model::Module &model, const syntax::Content &content,
           const syntax::Content &original, const LibraryEmission &linked) {
  if (const auto *module = std::get_if<syntax::Module>(&content))
    return Checker(model, *module, std::get_if<syntax::Module>(&original),
                   linked)
        .run();
  else {
    model.construction = std::get<source::Construction>(content);
    return true;
  }
}
} // namespace zkc::frontend::semantics
