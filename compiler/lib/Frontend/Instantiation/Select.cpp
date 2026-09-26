#include "Select.h"
#include "../Resolution/Declarations.h"
#include "../Resolution/Project.h"
#include "../Static/Domains.h"
#include "../Static/Naturals.h"
#include "../Syntax/Lexer.h"
#include "../Work.h"
#include "Work.h"
#include "zkc/Contracts/Bindings.h"
#include "llvm/ADT/STLExtras.h"
#include <limits>
#include <map>
#include <set>

using namespace llvm;
namespace zkc::frontend::instantiation {
using namespace syntax;
namespace {
using Substitution = std::map<std::string, std::string>;
using Names = std::set<std::string>;
constexpr unsigned maxDepth = 64, maxSpecializations = 1024;

class Selector {
  const Module &source;
  const resolution::Context &project;
  Module out;
  StringRef text, filename;
  Error error = Error::success();
  std::map<std::string, uint64_t> values;
  Names names;
  Names generatedOwners;
  std::map<std::string, size_t> nameCounts;
  std::map<std::string, const Protocol *> protocols;
  std::map<std::string, const Function *> functions;
  std::map<std::string, const Bundle *> bundles;
  std::map<std::string, const source::OperationBinding *> bindings;
  std::vector<std::string> stack;
  std::vector<Specialization> provenance;
  WorkBudget &budget;
  unsigned expansions = 0;

  bool good() { return !error; }
  bool fail(const source::Node &node, StringRef code, const Twine &message) {
    if (good())
      error = diagnostic(project.input, node.location.value_or(source::Span{}),
                         code, message);
    return false;
  }
  bool tick(const source::Node &node, uint64_t amount = 1) {
    return budget.charge(WorkAccount::AuthoredStatic, amount) ||
           fail(node, "source-staging-limit",
                "compiler work budget exhausted: authored-static");
  }
  bool declare(StringRef name, const source::Node &node) {
    return names.insert(name.str()).second ||
           fail(node, "source-static-duplicate",
                "duplicate declaration '" + name + "'");
  }
  bool isConstant(const Atom &a, const Names &locals = {}) {
    return a.kind == Atom::Kind::Name && !locals.count(a.value) &&
           values.count(a.value);
  }
  void replaceNatural(std::string &value, const Atom &atom,
                      const Names &locals = {}) {
    if (isConstant(atom, locals))
      value = std::to_string(values.at(atom.value));
  }
  std::string term(const StaticTerm &term, const Substitution &sub) {
    if (!isDomainRoot(term.root.value, term.root.kind == Atom::Kind::String)) {
      fail(term.root, "source-static-sort",
           "unknown domain root; use :: for associated members");
      return {};
    }
    if (term.members.size() > maxDepth) {
      fail(term.root, "source-staging-limit",
           "static domain projection depth exceeds 64");
      return {};
    }
    std::string value = term.root.value;
    if (term.root.kind == Atom::Kind::Name)
      if (auto it = sub.find(value); it != sub.end())
        value = it->second;
    for (const auto &member : term.members) {
      auto associated = protocol::associatedIdentity(value, member);
      value = associated.empty() ? value + "." + member : associated.str();
    }
    return value;
  }
  // Requirement terms are already paths in the existing requirement grammar.
  // Match a complete parameter root, never arbitrary substrings of an identity.
  std::string requirementTerm(StringRef value, const Substitution &sub,
                              unsigned depth = 0) {
    if (depth > maxDepth) {
      fail(source, "source-staging-limit",
           "requirement projection depth exceeds 64");
      return {};
    }
    if (auto found = sub.find(value.str()); found != sub.end())
      return found->second;
    auto split = value.rsplit('.');
    if (split.first == value || split.first.empty())
      return value.str();
    std::string root = requirementTerm(split.first, sub, depth + 1);
    auto associated = protocol::associatedIdentity(root, split.second);
    return associated.empty() ? root + "." + split.second.str()
                              : associated.str();
  }
  void type(syntax::Type &t, const Substitution &sub,
            bool domainPosition = false) {
    if (!tick(t))
      return;
    if ((domainPosition || !t.members.empty()) &&
        !isDomainRoot(t.name, t.quoted)) {
      fail(t, "source-type-domain",
           "unknown domain root; use :: for associated members");
      return;
    }
    // A bare type head names a logical constructor or a nominal record, even
    // if a domain parameter has the same spelling. Substitute only a domain
    // argument or the root of an associated element type.
    if (!t.quoted && (domainPosition || !t.members.empty()))
      if (auto found = sub.find(t.name); found != sub.end())
        t.name = found->second;
    const bool elementArgument = t.name == "Vector" || t.name == "Matrix";
    for (auto &arg : t.arguments)
      type(arg, sub, !elementArgument && !t.product);
  }
  std::string symbolicSort(StringRef value, unsigned depth = 0) {
    if (depth > maxDepth) {
      fail(source, "source-staging-limit",
           "domain sort projection depth exceeds 64");
      return {};
    }
    if (value == "Field" || value == "Group" || value == "Commitment" ||
        value == "Transcript" || value == "Codec")
      return value.str();
    auto split = value.rsplit('.');
    if (split.first == value || split.first.empty())
      return {};
    return protocol::associatedMemberSort(symbolicSort(split.first),
                                          split.second)
        .str();
  }
  std::string boundSort(StringRef bound, const source::Node &node) {
    std::string result;
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
        if (!result.empty()) {
          fail(node, "source-bound-sort", "ambiguous capability sort");
          return {};
        }
        result = sort.str();
      }
    }
    if (result.empty())
      fail(node, "source-bound", "unknown unary capability '" + bound + "'");
    return result;
  }
  bool requirements(ArrayRef<source::Requirement> reqs, const Substitution &sub,
                    const source::Node &node, unsigned depth = 0,
                    bool closed = true,
                    const std::vector<std::vector<StaticTerm>> &metadata = {}) {
    if (depth > maxDepth)
      return fail(node, "source-bundle-cycle",
                  "cyclic or too deep requirement bundle");
    for (size_t reqIndex = 0; reqIndex < reqs.size(); ++reqIndex) {
      const auto &req = reqs[reqIndex];
      auto resolve = [&](size_t index) {
        if (reqIndex < metadata.size() && index < metadata[reqIndex].size()) {
          const auto &t = metadata[reqIndex][index];
          if (!isDomainRoot(t.root.value, t.root.kind == Atom::Kind::String))
            return std::string{};
          // An opaque quoted root is never a reference to a formal parameter.
          if (t.root.kind == Atom::Kind::String) {
            if (!closed)
              return std::string{};
            return term(t, {});
          }
        }
        if (!closed) {
          StringRef root = req.arguments[index];
          unsigned projections = 0;
          while (!sub.count(root.str()) && root.contains('.')) {
            if (++projections > maxDepth) {
              fail(req, "source-staging-limit",
                   "requirement projection depth exceeds 64");
              return std::string{};
            }
            root = root.rsplit('.').first;
          }
          if (!sub.count(root.str()))
            return std::string{};
        }
        return requirementTerm(req.arguments[index], sub);
      };
      if (!tick(req))
        return false;
      auto foundBundle = bundles.find(req.predicate);
      if (foundBundle != bundles.end()) {
        const auto *bundle = foundBundle->second;
        if (bundle->parameters.size() != req.arguments.size())
          return fail(req, "source-bundle-arity",
                      "requirement bundle arity mismatch");
        Substitution nested;
        for (auto [index, key] : enumerate(bundle->parameters))
          nested.emplace(key, resolve(index));
        if (!requirements(bundle->requirements, nested, req, depth + 1, closed,
                          bundle->requirementTerms))
          return false;
        continue;
      }
      generic::Signature signature;
      std::vector<std::string> selected;
      std::vector<unsigned> indices;
      for (size_t index = 0; index < req.arguments.size(); ++index) {
        auto value = resolve(index);
        auto sort = closed ? protocol::installedIdentitySort(value).str()
                           : symbolicSort(value);
        if (sort.empty())
          return fail(req, "source-static-domain",
                      "unknown requirement domain '" + value + "'");
        indices.push_back(selected.size());
        signature.scope.terms.push_back({value, {}});
        signature.scope.sorts.push_back(sort);
        selected.push_back(value);
      }
      if (req.predicate == "=") {
        if (selected.size() != 2)
          return fail(req, "generic-predicate-arity",
                      "equality needs two domains");
        if (signature.scope.sorts[0] != signature.scope.sorts[1])
          return fail(req, "generic-equality-sort",
                      "equality needs equal domain sorts");
        signature.requirements.push_back(requirements::Predicate::equal(0, 1));
      } else
        signature.requirements.push_back(
            requirements::Predicate::holds(req.predicate, indices));
      if (auto e = protocol::checkStaticVocabulary(signature))
        return fail(req, "source-static-requirement", toString(std::move(e)));
      if (closed)
        if (auto e = protocol::checkClosedRequirements(signature.requirements,
                                                       selected))
          return fail(req, "source-static-requirement", toString(std::move(e)));
    }
    return good();
  }
  bool declaration(const Protocol &p) {
    if (!p.generic)
      return true;
    if (source.profile)
      return fail(p, "source-profile-generic",
                  "protocol families require an explicit module");
    if (p.staticParameters.size() > 128 || p.requirements.size() > 1024)
      return fail(p, "source-staging-limit",
                  "protocol static contract exceeds budget");
    Substitution sorts;
    for (const auto &param : p.staticParameters) {
      std::string sort = param.sort.value_or("");
      for (const auto &bound : param.bounds) {
        auto candidate = boundSort(bound, param);
        if (!good())
          return false;
        if (!sort.empty() && sort != candidate)
          return fail(param, "source-bound-sort",
                      "incompatible capability sorts");
        sort = candidate;
      }
      if (symbolicSort(sort).empty())
        return fail(param, "generic-declared-sort", "unknown domain sort");
      if (!sorts.emplace(param.name, sort).second)
        return fail(param, "generic-duplicate-parameter",
                    "duplicate protocol domain parameter");
    }
    return requirements(p.requirements, sorts, p, 0, false, p.requirementTerms);
  }
  bool arguments(const Protocol &p, const source::Assignments &actuals,
                 const std::vector<StaticTerm> &terms,
                 const Substitution &outer, Substitution &sub,
                 const source::Node &node) {
    if (p.staticParameters.size() > 128 || p.requirements.size() > 1024)
      return fail(node, "source-staging-limit",
                  "protocol static contract exceeds budget");
    if (actuals.size() != p.staticParameters.size())
      return fail(
          node, "source-static-arity",
          "protocol specialization requires every named domain argument");
    for (auto [i, arg] : enumerate(actuals)) {
      auto value = i < terms.size() ? term(terms[i], outer) : arg.second;
      if (!sub.emplace(arg.first, value).second)
        return fail(node, "source-static-argument",
                    "duplicate named domain argument");
    }
    Names formals;
    std::vector<source::Requirement> bounds = p.requirements;
    for (const auto &param : p.staticParameters) {
      if (!formals.insert(param.name).second)
        return fail(param, "generic-duplicate-parameter",
                    "duplicate protocol domain parameter");
      auto actual = sub.find(param.name);
      if (actual == sub.end())
        return fail(node, "source-static-argument",
                    "missing domain argument '" + param.name + "'");
      std::string sort = param.sort.value_or("");
      for (const auto &bound : param.bounds) {
        auto candidate = boundSort(bound, param);
        if (!sort.empty() && sort != candidate)
          return fail(param, "source-bound-sort",
                      "incompatible capability sorts");
        sort = candidate;
        source::Requirement req;
        req.location = param.location;
        req.predicate = bound;
        req.arguments = {param.name};
        bounds.push_back(std::move(req));
      }
      if (!good())
        return false;
      if (sort.empty() ||
          protocol::installedIdentitySort(actual->second) != sort)
        return fail(node, "source-static-sort",
                    "wrong or unknown domain for '" + param.name + "'");
    }
    return requirements(bounds, sub, node, 0, true, p.requirementTerms);
  }
  std::string generated(StringRef owner, StringRef kind, StringRef site) {
    bool nested = generatedOwners.count(owner.str());
    if ((nested ? owner.size() : 2 * owner.size()) + 2 * site.size() > 65500) {
      fail(source, "source-staging-limit",
           "generated declaration name exceeds 64 KiB");
      return {};
    }
    // The independent generic carrier requires dot-free declaration names.
    // Hex encodes UTF-8 bytes injectively; underscores separate components
    // and can never occur in an encoded component.
    auto hex = [](StringRef value) {
      std::string encoded;
      encoded.reserve(2 * value.size());
      for (unsigned char byte : value.bytes()) {
        encoded += "0123456789abcdef"[byte >> 4];
        encoded += "0123456789abcdef"[byte & 15];
      }
      return encoded;
    };
    // Extend a path we generated structurally. Never parse a user's spelling
    // as a generated prefix, and never repeatedly hex-encode an enclosing path.
    std::string result = (nested ? owner.str() : "__stage_" + hex(owner)) +
                         "_" + kind.str() + "_" + hex(site);
    generatedOwners.insert(result);
    return result;
  }
  bool reserveExpansion(const source::Node &node) {
    return ++expansions <= maxSpecializations ||
           fail(node, "source-staging-limit", "more than 1024 specializations");
  }
  void attributes(source::Names &attrs, const std::vector<Atom> &atoms,
                  StringRef callee, bool qualified, const Names &locals) {
    // Only operation-owned natural slots, never labels, codecs or arbitrary
    // user function attributes. Unknown slots retain their original spelling.
    std::string op = callee.str();
    if (!qualified) {
      auto selected = bindings.find(callee.str());
      if (selected == bindings.end())
        return;
      op = selected->second->application.contract;
    }
    for (size_t i = 0; i < attrs.size() && i < atoms.size(); ++i) {
      bool numeric =
          ((op == "index.constant" || op == "vector.splat" ||
            op == "vector.powers" || op == "vector.at" ||
            op == "vector.length_check" || op == "poly.degree_check" ||
            op == "random.vector" || op == "curve.at") &&
           i == 0) ||
          (op == "matrix.shape_check" && i < 2) ||
          (op == "vector.matvec" && i < 3);
      if (numeric)
        replaceNatural(attrs[i], atoms[i], locals);
    }
  }
  void statics(std::optional<source::Names> &args,
               const std::vector<StaticTerm> &terms, const Substitution &sub) {
    if (!args)
      return;
    for (size_t i = 0; i < args->size() && i < terms.size(); ++i)
      (*args)[i] = term(terms[i], sub);
  }
  void expression(Expression &e, const Substitution &sub, const Names &locals) {
    if (!tick(e))
      return;
    if (e.kind == Expression::Kind::Name && !e.quoted &&
        !locals.count(e.name)) {
      if (auto found = values.find(e.name); found != values.end()) {
        e.kind = Expression::Kind::Index;
        e.name = std::to_string(found->second);
      }
    }
    statics(e.staticArguments, e.staticTerms, sub);
    attributes(e.attributes, e.attributeAtoms, e.name, e.qualified, locals);
    e.attributeAtoms.clear();
    for (auto &arg : e.operands)
      expression(arg, sub, locals);
    if (e.traversal) {
      e.traversal = std::make_shared<LexicalTraversal>(*e.traversal);
      auto nested = locals;
      nested.insert(e.traversal->element);
      if (!e.traversal->state.empty())
        nested.insert(e.traversal->state);
      Names parameters;
      for (const auto &[name, value] : sub)
        parameters.insert(name);
      body(e.traversal->body, sub, std::move(nested), parameters, "traversal");
    }
  }
  void localCall(Call &call, const Substitution &sub, StringRef owner,
                 StringRef site, const Names &locals) {
    statics(call.staticArguments, call.staticTerms, sub);
    attributes(call.attributes, call.attributeAtoms, call.callee,
               call.qualified, locals);
    call.attributeAtoms.clear();
    if (call.annotation)
      for (auto &t : *call.annotation)
        type(t, sub);
    if (!call.role || call.qualified || !call.staticArguments)
      return;
    auto target = functions.find(call.callee);
    if (target == functions.end() || !target->second->generic)
      return;
    const auto &f = *target->second;
    if (f.parameters.size() != call.staticArguments->size()) {
      fail(call, "source-static-arity",
           "explicit function instantiation arity mismatch");
      return;
    }
    if (!reserveExpansion(call))
      return;
    source::Configuration config;
    config.location = call.location;
    config.name = generated(owner, "fn", site);
    if (!declare(config.name, call))
      return;
    config.base = call.callee;
    for (auto [param, actual] : zip(f.parameters, *call.staticArguments))
      config.arguments.emplace_back(param.name, actual);
    out.configurations.push_back(config);
    call.callee = config.name;
    call.staticArguments.reset();
    call.staticTerms.clear();
  }
  void body(Body &body, const Substitution &sub, Names locals,
            const Names &parameters, StringRef owner) {
    for (auto &instruction : body) {
      if (!good() || !tick(instruction))
        return;
      if (auto *call = std::get_if<Call>(&instruction.value)) {
        localCall(*call, sub, owner, instruction.site, locals);
        bool constantInput = false;
        for (const auto &atom : call->inputAtoms)
          constantInput |= isConstant(atom, locals);
        if (constantInput && !call->role) {
          Binding b;
          b.location = call->location;
          b.outputs = call->outputs;
          b.destructure = call->destructure;
          b.annotation = call->annotation;
          b.expression.location = call->location;
          b.expression.kind = call->isOperator ? Expression::Kind::Operator
                                               : Expression::Kind::Call;
          b.expression.name = call->callee;
          b.expression.qualified = call->qualified;
          b.expression.quoted = call->quoted;
          b.expression.staticArguments = call->staticArguments;
          b.expression.staticTerms = call->staticTerms;
          b.expression.attributes = call->attributes;
          b.expression.argumentNames = call->argumentNames;
          for (const auto &atom : call->inputAtoms) {
            Expression e;
            e.location = atom.location;
            e.name = atom.value;
            e.quoted = atom.kind == Atom::Kind::String;
            b.expression.operands.push_back(e);
          }
          expression(b.expression, {}, locals);
          locals.insert(b.outputs.begin(), b.outputs.end());
          instruction.value = std::move(b);
        } else {
          locals.insert(call->outputs.begin(), call->outputs.end());
        }
      } else if (auto *binding = std::get_if<Binding>(&instruction.value)) {
        expression(binding->expression, sub, locals);
        if (binding->annotation)
          for (auto &t : *binding->annotation)
            type(t, sub);
        locals.insert(binding->outputs.begin(), binding->outputs.end());
      } else if (auto *placement = std::get_if<Placement>(&instruction.value)) {
        if (placement->annotation)
          type(*placement->annotation, sub);
        this->body(placement->body, sub, locals, parameters, owner);
        locals.insert(placement->outputs.begin(), placement->outputs.end());
      } else if (auto *ret = std::get_if<Exit>(&instruction.value)) {
        expression(ret->expression, sub, locals);
      } else if (auto *loop = std::get_if<Loop>(&instruction.value)) {
        Names shadowed = parameters;
        shadowed.insert(locals.begin(), locals.end());
        if (loop->countAtom && isConstant(*loop->countAtom, shadowed)) {
          replaceNatural(loop->count.value, *loop->countAtom, shadowed);
          loop->count.kind = source::LoopCount::Kind::Constant;
        }
        auto inner = locals;
        for (const auto &pair : loop->carried)
          inner.insert(pair.first);
        this->body(loop->body, sub, inner, parameters, owner);
        locals.insert(loop->outputs.begin(), loop->outputs.end());
      } else if (auto *loop = std::get_if<For>(&instruction.value)) {
        expression(loop->lower, sub, locals);
        expression(loop->upper, sub, locals);
        auto inner = locals;
        inner.insert(loop->induction);
        for (const auto &pair : loop->carried)
          inner.insert(pair.first);
        this->body(loop->body, sub, inner, parameters, owner);
        locals.insert(loop->outputs.begin(), loop->outputs.end());
      } else if (auto *branch = std::get_if<Conditional>(&instruction.value)) {
        expression(branch->condition, sub, locals);
        this->body(branch->thenBody, sub, locals, parameters, owner);
        this->body(branch->elseBody, sub, locals, parameters, owner);
        locals.insert(branch->outputs.begin(), branch->outputs.end());
      } else if (auto *call =
                     std::get_if<syntax::Invocation>(&instruction.value)) {
        locals.insert(call->outputs.begin(), call->outputs.end());
      } else if (auto *message =
                     std::get_if<source::Message>(&instruction.value)) {
        locals.insert(message->output);
      }
    }
  }
  void protocolBody(Protocol &p, const Substitution &sub) {
    Names locals, parameters(p.parameters.begin(), p.parameters.end());
    for (const auto &entry : sub)
      locals.insert(entry.first);
    for (auto &arg : p.arguments) {
      type(arg.type, sub);
      locals.insert(arg.name);
    }
    for (auto &result : p.results)
      type(result.type, sub);
    if (p.body)
      body(*p.body, sub, locals, parameters, p.name);
    for (auto &dep : p.dependencies) {
      auto args = p.dependencyArguments.find(dep.name);
      if (args == p.dependencyArguments.end()) {
        auto found = protocols.find(dep.protocol);
        if (found != protocols.end() && found->second->generic)
          fail(dep, "source-static-required",
               "generic dependency requires explicit domain arguments");
        continue;
      }
      auto found = protocols.find(dep.protocol);
      if (found == protocols.end() || !found->second->generic) {
        fail(dep, "source-static-target",
             "specialised dependency requires a generic protocol");
        return;
      }
      auto name = generated(p.name, "dep", dep.name);
      if (!declare(name, dep))
        return;
      specialize(*found->second, name, args->second.arguments,
                 args->second.terms, sub, dep);
      dep.protocol = name;
    }
    p.dependencyArguments.clear();
  }
  void specialize(const Protocol &definition, StringRef emitted,
                  const source::Assignments &actuals,
                  const std::vector<StaticTerm> &terms,
                  const Substitution &outer, const source::Node &node) {
    if (!good() || !reserveExpansion(node))
      return;
    if (stack.size() >= maxDepth) {
      fail(node, "source-specialization-depth",
           "specialization depth exceeds 64");
      return;
    }
    if (llvm::is_contained(stack, definition.name)) {
      fail(node, "source-specialization-cycle",
           "recursive protocol generation is forbidden");
      return;
    }
    Substitution sub;
    if (!arguments(definition, actuals, terms, outer, sub, node))
      return;
    stack.push_back(definition.name);
    for (auto count : {definition.roles.size(), definition.parameters.size(),
                       definition.arguments.size(), definition.results.size(),
                       definition.dependencies.size()})
      if (!tick(node, count))
        return;
    if (!chargeDeclarationCopy(budget, definition)) {
      fail(node, "source-staging-limit",
           "compiler work budget exhausted: authored-static");
      return;
    }
    Protocol p = definition;
    p.name = emitted.str();
    p.generic = false;
    p.staticParameters.clear();
    p.requirements.clear();
    p.requirementTerms.clear();
    Specialization record;
    record.location = node.location;
    record.definition = definition.name;
    record.emitted = p.name;
    for (const auto &param : definition.staticParameters)
      record.arguments.push_back({param.name, sub.at(param.name)});
    protocolBody(p, sub);
    stack.pop_back();
    if (!good())
      return;
    provenance.push_back(std::move(record));
    out.protocols.push_back(std::move(p));
  }

  std::string
  entryInstance(const Protocol &p, StringRef entry, StringRef path,
                const std::map<std::string, const Protocol *> &selected,
                const source::Node &node, std::vector<std::string> &ancestry) {
    if (ancestry.size() >= maxDepth || llvm::is_contained(ancestry, p.name)) {
      fail(node, "source-specialization-cycle",
           "direct entry has a recursive or excessively deep dependency");
      return {};
    }
    if (!p.parameters.empty()) {
      fail(node, "source-entry-parameters",
           "a protocol with natural parameters requires an explicit instance");
      return {};
    }
    if (!reserveExpansion(node))
      return {};
    ancestry.push_back(p.name);
    source::Instance result;
    result.location = node.location;
    result.name = generated(entry, "instance", path);
    if (!declare(result.name, node))
      return {};
    result.protocol = p.name;
    for (const auto &role : p.roles)
      result.roles.emplace_back(role, role);
    for (const auto &dep : p.dependencies) {
      auto child = selected.find(dep.protocol);
      if (child == selected.end()) {
        fail(node, "source-entry-dependency",
             "direct entry requires every dependency to resolve to a protocol");
        return {};
      }
      auto instance = entryInstance(
          *child->second, entry,
          (path + ":" + Twine(dep.name.size()) + ":" + dep.name).str(),
          selected, node, ancestry);
      if (!good())
        return {};
      result.dependencies.emplace_back(dep.name, instance);
    }
    ancestry.pop_back();
    auto name = result.name;
    out.instances.push_back(std::move(result));
    return name;
  }

public:
  Selector(const Module &source, const resolution::Context &project,
           StringRef text, StringRef filename, WorkBudget &budget)
      : source(source), project(project), text(text), filename(filename),
        budget(budget) {}
  Expected<Selection> run(ArrayRef<std::string> reservedNames) {
    // Snapshot admission charges declarations before copying them; recursive
    // staging operations below have their own charges.
    if (!tick(source))
      return std::move(error);
    resolution::declarations(source, [&](const auto &d, auto) {
      if (good() && !chargeDeclarationCopy(budget, d))
        fail(d, "source-staging-limit",
             "compiler work budget exhausted: authored-static");
    });
    if (!good())
      return std::move(error);
    out = source;
    for (const auto &name : reservedNames) {
      names.insert(name);
      ++nameCounts[name];
    }
    // Only additions need staging's global collision check. Existing modules
    // without static construction retain their previous admission boundary.
    auto reserve = [&](const auto &section) {
      for (const auto &d : section) {
        names.insert(d.name);
        ++nameCounts[d.name];
      }
    };
    reserve(source.bindings);
    reserve(source.functions);
    reserve(source.protocols);
    reserve(source.configurations);
    reserve(source.instances);
    reserve(source.entries);
    reserve(source.structs);
    reserve(source.bundles);
    reserve(source.relations);
    reserve(source.imports);
    reserve(source.relationViews);
    for (const auto &b : source.bundles)
      bundles.emplace(b.name, &b);
    for (const auto &b : source.bindings)
      bindings.emplace(b.name, &b);
    for (const auto &c : source.constants)
      if (!declare(c.name, c))
        return std::move(error);
    auto evaluated = static_eval::evaluateNaturals(
        source.constants, text, filename, &project.input, budget);
    if (!evaluated)
      return evaluated.takeError();
    values = std::move(*evaluated);
    for (const auto &p : source.protocols) {
      if (!declaration(p))
        return std::move(error);
      if ((p.generic && nameCounts[p.name] != 1) ||
          !protocols.emplace(p.name, &p).second) {
        fail(p, "source-duplicate", "duplicate protocol definition");
        return std::move(error);
      }
    }
    for (const auto &f : source.functions) {
      if (!f.effects.empty()) {
        fail(f, "source-effects",
             "effect clauses are supported only by checked library bodies");
        return std::move(error);
      }
      functions.emplace(f.name, &f);
    }
    out.protocols.clear();
    out.configurations.clear();
    out.constants.clear();
    for (const auto &config : source.configurations) {
      auto metadata = source.configurationTerms.find(config.name);
      if (metadata != source.configurationTerms.end())
        for (const auto &argument : metadata->second)
          if (!isDomainRoot(argument.root.value,
                            argument.root.kind == Atom::Kind::String))
            fail(argument.root, "source-static-sort",
                 "unknown domain root; use :: for associated members");
      if (!good())
        break;
      auto target = protocols.find(config.base);
      if (target == protocols.end()) {
        out.configurations.push_back(config);
        continue;
      }
      if (!target->second->generic || !config.implementations.empty()) {
        fail(config, "source-static-target",
             "protocol configure requires a generic definition and no "
             "implementation selection");
        break;
      }
      // The source's own configure name is intentionally the public protocol
      // identity. It must not collide with any non-configuration declaration.
      if (nameCounts[config.name] != 1) {
        fail(config, "source-static-duplicate",
             "specialization name is already declared");
        break;
      }
      specialize(*target->second, config.name, config.arguments,
                 metadata == source.configurationTerms.end()
                     ? std::vector<StaticTerm>{}
                     : metadata->second,
                 {}, config);
    }
    for (const auto &definition : source.protocols) {
      if (definition.generic)
        continue;
      if (!definition.requirements.empty()) {
        fail(definition, "source-static-contract",
             "protocol requirements need a generic parameter list");
        break;
      }
      auto p = definition;
      protocolBody(p, {});
      out.protocols.push_back(std::move(p));
    }
    for (auto &f : out.functions) {
      Names locals;
      for (const auto &parameter : f.parameters)
        locals.insert(parameter.name);
      for (const auto &arg : f.arguments)
        locals.insert(arg.name);
      if (f.body)
        body(*f.body, {}, locals, {}, f.name);
    }
    for (auto &entry : out.entries) {
      auto arguments = source.entryArguments.find(entry.name);
      if (arguments == source.entryArguments.end())
        continue;
      auto target = protocols.find(entry.instance);
      if (target == protocols.end() || !target->second->generic) {
        fail(entry, "source-entry-target",
             "entry specialization requires a generic protocol");
        break;
      }
      auto selected = generated(entry.name, "protocol", "root");
      if (!declare(selected, entry))
        break;
      specialize(*target->second, selected, arguments->second.arguments,
                 arguments->second.terms, {}, entry);
      entry.instance = selected;
    }
    std::map<std::string, const Protocol *> selectedProtocols;
    for (const auto &p : out.protocols)
      selectedProtocols.emplace(p.name, &p);
    for (auto &entry : out.entries) {
      auto target = selectedProtocols.find(entry.instance);
      if (target == selectedProtocols.end())
        continue;
      std::vector<std::string> ancestry;
      entry.instance = entryInstance(*target->second, entry.name, "root",
                                     selectedProtocols, entry, ancestry);
      if (!good())
        break;
    }
    for (auto &i : out.instances) {
      auto projection = source.instanceProtocolTerms.find(i.name);
      if (projection != source.instanceProtocolTerms.end() &&
          !projection->second.members.empty()) {
        const auto &path = projection->second;
        if (path.members.size() > maxDepth) {
          fail(path.root, "source-staging-limit",
               "instance protocol projection exceeds 64 members");
          break;
        }
        auto selected = selectedProtocols.find(path.root.value);
        for (const auto &member : path.members) {
          if (selected == selectedProtocols.end())
            break;
          const auto &deps = selected->second->dependencies;
          auto dep = llvm::find_if(deps, [&](const source::Dependency &d) {
            return d.name == member;
          });
          if (dep == deps.end()) {
            selected = selectedProtocols.end();
            break;
          }
          selected = selectedProtocols.find(dep->protocol);
        }
        if (selected == selectedProtocols.end()) {
          fail(path.root, "source-static-projection",
               "instance projection requires a concrete protocol and declared "
               "dependency aliases");
          break;
        }
        i.protocol = selected->second->name;
      }
      auto target = protocols.find(i.protocol);
      if (target != protocols.end() && target->second->generic)
        fail(i, "source-static-required",
             "instances must name a configured concrete protocol");
      auto metadata = source.instanceParameterAtoms.find(i.name);
      if (metadata == source.instanceParameterAtoms.end())
        continue;
      for (auto [j, arg] : enumerate(i.parameters)) {
        if (j >= metadata->second.size())
          continue;
        const auto &a = metadata->second[j];
        if (auto *ingress = std::get_if<source::FamilyIngress>(&arg.second)) {
          if (a.kind != Atom::Kind::Number && !isConstant(a))
            fail(a, "source-constant-reference",
                 "ingress bound requires a natural constant");
          replaceNatural(ingress->bound, a);
          continue;
        }
        if (a.kind != Atom::Kind::Number && !isConstant(a))
          fail(a, "source-constant-reference",
               "instance natural parameter requires a number or bare constant");
        replaceNatural(std::get<std::string>(arg.second), a);
      }
    }
    for (auto &view : out.relationViews) {
      auto metadata = source.relationViewHeights.find(view.name);
      if (metadata == source.relationViewHeights.end())
        continue;
      auto value = metadata->second.value;
      replaceNatural(value, metadata->second);
      if (metadata->second.kind == Atom::Kind::String ||
          StringRef(value).getAsInteger(10, view.height))
        fail(metadata->second, "source-constant-reference",
             "relation height requires a bounded natural constant");
    }
    if (!good())
      return std::move(error);
    out.instanceParameterAtoms.clear();
    out.instanceProtocolTerms.clear();
    out.relationViewHeights.clear();
    out.configurationTerms.clear();
    out.entryArguments.clear();
    out.quotedBases.clear();
    out.quotedRelations.clear();
    out.quotedInstances.clear();
    out.quotedInstanceDependencies.clear();
    out.quotedSelectors.clear();
    return Selection{std::move(out), std::move(provenance), std::move(values)};
  }
};
} // namespace
Expected<Selection> select(const Content &content,
                           const resolution::Context &project, StringRef text,
                           StringRef filename,
                           ArrayRef<std::string> reservedNames,
                           WorkBudget &budget) {
  if (const auto *module = std::get_if<Module>(&content))
    return Selector(*module, project, text, filename, budget)
        .run(reservedNames);
  if (auto error = work::charge(budget, WorkAccount::AuthoredStatic))
    return error;
  return Selection{content, {}, {}};
}
} // namespace zkc::frontend::instantiation
