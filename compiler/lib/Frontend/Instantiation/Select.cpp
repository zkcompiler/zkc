#include "Select.h"
#include "../Resolution/Declarations.h"
#include "../Resolution/Project.h"
#include "../Static/Attributes.h"
#include "../Static/Domains.h"
#include "../Static/Naturals.h"
#include "../Static/Structural.h"
#include "../Static/Types.h"
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
  std::map<std::string, syntax::Type> selectedTypes;
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
  // Replace a constant reference by its natural value.
  void replaceNatural(Atom &atom, const Names &locals = {}) {
    if (!isConstant(atom, locals))
      return;
    atom.value = std::to_string(values.at(atom.value));
    atom.kind = Atom::Kind::Number;
  }
  // A closed actual keeps its category in syntax: a natural, or an exact
  // installed identity. It never becomes a lexical reference.
  static Atom::Kind actualKind(StringRef value) {
    uint64_t number;
    return !value.getAsInteger(10, number) ? Atom::Kind::Number
                                           : Atom::Kind::String;
  }
  static std::string symbol(const Reference &reference) {
    return encode(reference.target);
  }
  std::string term(const StaticTerm &term, const Substitution &sub) {
    if (typeArgumentSyntax(term)) {
      auto expression = syntax::typeExpression(term);
      type(expression, sub);
      return syntax::staticSpelling(syntax::staticExpression(expression));
    }
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
    if (term.root.kind == Atom::Kind::Name) {
      if (auto it = sub.find(value); it != sub.end())
        value = it->second;
      else if (term.members.empty() && isConstant(term.root))
        return std::to_string(values.at(value));
    }
    for (const auto &member : term.members) {
      auto associated = protocol::associatedIdentity(value, member);
      value = associated.empty() ? value + "." + member : associated.str();
    }
    return value;
  }
  // Close a static term in place: substitute bound roots with their exact
  // actuals, evaluate a bare constant, and fold associated identities.
  // Its common spelling is then term(t, {}).
  void close(StaticTerm &t, const Substitution &sub) {
    if (typeArgumentSyntax(t)) {
      auto expression = syntax::typeExpression(t);
      type(expression, sub);
      t = syntax::staticExpression(expression);
      return;
    }
    if (!isDomainRoot(t.root.value, t.root.kind == Atom::Kind::String)) {
      fail(t.root, "source-static-sort",
           "unknown domain root; use :: for associated members");
      return;
    }
    if (t.members.size() > maxDepth) {
      fail(t.root, "source-staging-limit",
           "static domain projection depth exceeds 64");
      return;
    }
    if (t.root.kind == Atom::Kind::Name) {
      if (auto it = sub.find(t.root.value); it != sub.end()) {
        if (auto selected = selectedTypes.find(it->second);
            selected != selectedTypes.end() && t.members.empty()) {
          auto location = t.root.location;
          t = syntax::staticExpression(selected->second);
          t.root.location = location;
          return;
        }
        t.root.value = it->second;
        t.root.kind = actualKind(it->second);
      } else if (t.members.empty())
        replaceNatural(t.root);
    }
    while (!t.members.empty()) {
      auto associated =
          protocol::associatedIdentity(t.root.value, t.members.front());
      if (associated.empty())
        break;
      t.root.value = associated.str();
      t.root.kind = Atom::Kind::String;
      t.members.erase(t.members.begin());
    }
  }
  // A requirement argument under a (possibly symbolic) substitution. Match a
  // complete parameter root, never arbitrary substrings of an identity.
  std::string requirementTerm(const StaticTerm &t, const Substitution &sub) {
    if (t.members.size() > maxDepth) {
      fail(t.root, "source-staging-limit",
           "requirement projection depth exceeds 64");
      return {};
    }
    std::string value = t.root.value;
    if (t.root.kind == Atom::Kind::Name)
      if (auto found = sub.find(value); found != sub.end())
        value = found->second;
    for (const auto &member : t.members) {
      auto associated = protocol::associatedIdentity(value, member);
      value = associated.empty() ? value + "." + member : associated.str();
    }
    return value;
  }
  void type(syntax::Type &t, const Substitution &sub,
            bool domainPosition = false) {
    if (!tick(t))
      return;
    if ((domainPosition || !t.members.empty()) &&
        !isDomainRoot(t.name, t.quoted())) {
      fail(t, "source-type-domain",
           "unknown domain root; use :: for associated members");
      return;
    }
    if (!t.quoted() && !domainPosition && t.members.empty() &&
        t.arguments.empty())
      if (auto actual = sub.find(t.name); actual != sub.end())
        if (auto selected = selectedTypes.find(actual->second);
            selected != selectedTypes.end()) {
          auto location = t.location;
          t = selected->second;
          t.location = location;
          return;
        }
    // A bare type head names a logical constructor or a nominal record, even
    // if a domain parameter has the same spelling. Substitute only a domain
    // argument or the root of an associated element type.
    if (!t.quoted() && (domainPosition || !t.members.empty()))
      if (auto found = sub.find(t.name); found != sub.end()) {
        t.name = found->second;
        t.kind = actualKind(found->second);
      }
    const bool elementArgument = elementTypeFamily(t.name);
    const auto *declaration =
        protocol::typeDeclaration(logicalConstructor(t.name));
    for (size_t i = 0; i < t.arguments.size(); ++i) {
      auto &arg = t.arguments[i];
      bool domainArgument = !elementArgument && !t.product;
      if (declaration && i < declaration->parameters.size()) {
        auto kind = declaration->parameters[i].kind;
        domainArgument = kind == protocol::StaticKind::Domain;
        if (kind == protocol::StaticKind::Nat && !arg.quoted() &&
            arg.members.empty() && arg.arguments.empty()) {
          if (auto found = sub.find(arg.name); found != sub.end())
            arg.name = found->second;
          if (auto found = values.find(arg.name); found != values.end())
            arg.name = std::to_string(found->second);
          uint64_t number;
          if (!StringRef(arg.name).getAsInteger(10, number))
            arg.kind = Atom::Kind::Number;
        }
      }
      type(arg, sub, domainArgument);
    }
  }
  std::string typeIdentity(const syntax::Type &t, unsigned depth = 0) {
    if (depth > 8 || !tick(t)) {
      fail(t, "source-static-sort",
           "Type argument exceeds the structural depth bound");
      return {};
    }
    std::string kind;
    source::Names arguments;
    if (!t.members.empty() && t.arguments.empty()) {
      auto root = syntax::staticExpression(t);
      auto member = root.members.back();
      root.members.pop_back();
      auto domain = term(root, {});
      kind = associatedTypeConstructor(protocol::installedIdentitySort(domain),
                                       member)
                 .str();
      arguments.push_back(domain);
    } else if (elementTypeFamily(t.name) && t.arguments.size() == 1) {
      auto element = typeIdentity(t.arguments.front(), depth + 1);
      if (!good())
        return {};
      auto parsed = protocol::parseBoundType(element, false);
      if (!parsed) {
        consumeError(parsed.takeError());
        fail(t, "source-static-sort", "invalid type-family element");
        return {};
      }
      kind = familyResultConstructor(t.name, parsed->kind).str();
      arguments.push_back(parsed->identity);
    } else {
      kind = logicalConstructor(t.name).str();
      const auto *declaration = protocol::typeDeclaration(kind);
      if (!declaration || !declaration->common || t.product || t.quoted() ||
          t.natural() || t.arguments.size() != declaration->parameters.size()) {
        fail(t, "source-static-sort",
             "expected a closed logical Type argument");
        return {};
      }
      for (auto [parameter, child] :
           zip(declaration->parameters, t.arguments)) {
        if (parameter.kind == protocol::StaticKind::Type)
          arguments.push_back(typeIdentity(child, depth + 1));
        else {
          auto value = term(syntax::staticExpression(child), {});
          if (parameter.kind == protocol::StaticKind::Nat &&
              (child.quoted() || !child.members.empty() ||
               !child.arguments.empty())) {
            fail(child, "source-static-sort",
                 "expected a natural Type argument");
            return {};
          }
          arguments.push_back(value);
        }
        if (!good())
          return {};
      }
    }
    if (kind.empty()) {
      fail(t, "source-static-sort",
           "unknown Type constructor or associated type");
      return {};
    }
    auto checked =
        protocol::parseBoundType(logicalSpelling(kind, arguments), false);
    if (!checked) {
      consumeError(checked.takeError());
      fail(t, "source-static-sort", "invalid closed logical Type argument");
      return {};
    }
    return checked->spelling();
  }
  std::string symbolicSort(StringRef value, unsigned depth = 0) {
    if (depth > maxDepth) {
      fail(source, "source-staging-limit",
           "domain sort projection depth exceeds 64");
      return {};
    }
    if (value == "Type" || value == "Nat")
      return value.str();
    if (llvm::is_contained(protocol::domainSorts(), value))
      return value.str();
    auto split = value.rsplit('.');
    if (split.first == value || split.first.empty())
      return {};
    return protocol::associatedMemberSort(symbolicSort(split.first, depth + 1),
                                          split.second)
        .str();
  }
  std::string boundSort(StringRef bound, const source::Node &node) {
    if (bound == "Type" || bound == "Nat" || bound == "nat")
      return bound == "Type" ? "Type" : "Nat";
    auto candidates = capabilityDomainSorts(bound);
    if (candidates.size() > 1) {
      fail(node, "source-bound-sort", "ambiguous capability sort");
      return {};
    }
    if (candidates.empty()) {
      fail(node, "source-bound", "unknown unary capability '" + bound + "'");
      return {};
    }
    return candidates.front();
  }

  bool requirements(ArrayRef<syntax::Requirement> reqs, const Substitution &sub,
                    const source::Node &node, unsigned depth = 0,
                    bool closed = true) {
    if (depth > maxDepth)
      return fail(node, "source-bundle-cycle",
                  "cyclic or too deep requirement bundle");
    for (const auto &req : reqs) {
      auto resolve = [&](size_t index) {
        const auto &t = req.arguments[index];
        if (!isDomainRoot(t.root.value, t.root.kind == Atom::Kind::String))
          return std::string{};
        // An opaque quoted root is never a reference to a formal parameter.
        if (t.root.kind == Atom::Kind::String)
          return closed ? term(t, {}) : std::string{};
        if (!closed && !sub.count(t.root.value))
          return std::string{};
        return requirementTerm(t, sub);
      };
      if (!tick(req))
        return false;
      if (req.predicate)
        if (auto found = bundles.find(symbol(*req.predicate));
            found != bundles.end()) {
          const auto *bundle = found->second;
          if (bundle->parameters.size() != req.arguments.size())
            return fail(req, "source-bundle-arity",
                        "requirement bundle arity mismatch");
          Substitution nested;
          for (auto [index, key] : enumerate(bundle->parameters))
            nested.emplace(key, resolve(index));
          if (!requirements(bundle->requirements, nested, req, depth + 1,
                            closed))
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
      if (!req.predicate) {
        if (selected.size() != 2)
          return fail(req, "generic-predicate-arity",
                      "equality needs two domains");
        if (signature.scope.sorts[0] != signature.scope.sorts[1])
          return fail(req, "generic-equality-sort",
                      "equality needs equal domain sorts");
        signature.requirements.push_back(requirements::Predicate::equal(0, 1));
      } else
        signature.requirements.push_back(
            requirements::Predicate::holds(symbol(*req.predicate), indices));
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
    if (p.staticParameters.size() > 128 || p.requirements.size() > 1024)
      return fail(p, "source-staging-limit",
                  "protocol static contract exceeds budget");
    Substitution sorts;
    for (const auto &param : p.staticParameters) {
      std::string sort = param.sort.value_or("");
      for (const auto &bound : param.bounds) {
        auto candidate = boundSort(symbol(bound), param);
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
    return requirements(p.requirements, sorts, p, 0, false);
  }
  bool arguments(const Protocol &p, const StaticAssignments &actuals,
                 const Substitution &outer, Substitution &sub,
                 const source::Node &node) {
    if (p.staticParameters.size() > 128 || p.requirements.size() > 1024)
      return fail(node, "source-staging-limit",
                  "protocol static contract exceeds budget");
    if (actuals.size() != p.staticParameters.size())
      return fail(
          node, "source-static-arity",
          "protocol specialization requires every named domain argument");
    for (const auto &[name, actual] : actuals)
      if (!sub.emplace(name, term(actual, outer)).second)
        return fail(node, "source-static-argument",
                    "duplicate named domain argument");
    Names formals;
    std::vector<syntax::Requirement> bounds = p.requirements;
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
        auto candidate = boundSort(symbol(bound), param);
        if (!sort.empty() && sort != candidate)
          return fail(param, "source-bound-sort",
                      "incompatible capability sorts");
        sort = candidate;
        if (sort == "Type" || sort == "Nat")
          continue;
        syntax::Requirement req;
        req.location = param.location;
        req.predicate = bound;
        StaticTerm subject;
        subject.root.value = param.name;
        subject.root.location = param.location;
        req.arguments = {std::move(subject)};
        bounds.push_back(std::move(req));
      }
      if (!good())
        return false;
      size_t index = llvm::find_if(actuals,
                                   [&](const auto &entry) {
                                     return entry.first == param.name;
                                   }) -
                     actuals.begin();
      if (sort == "Type") {
        auto selected = syntax::typeExpression(actuals[index].second);
        type(selected, outer);
        actual->second = typeIdentity(selected);
        if (!good())
          return false;
        selectedTypes.emplace(actual->second, std::move(selected));
        continue;
      }
      if (sort == "Nat") {
        uint64_t number;
        const auto &written = actuals[index].second;
        if (StringRef(actual->second).getAsInteger(10, number) ||
            number > 1048576 || written.root.kind == Atom::Kind::String ||
            !written.members.empty() || !written.arguments.empty())
          return fail(node, "source-static-sort",
                      "expected a bounded natural argument");
        actual->second = std::to_string(number);
        continue;
      }
      if (sort.empty() ||
          protocol::installedIdentitySort(actual->second) != sort)
        return fail(node, "source-static-sort",
                    "wrong or unknown domain for '" + param.name + "'");
    }
    return requirements(bounds, sub, node, 0, true);
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
  void attributes(std::vector<Atom> &atoms, const Target &callee,
                  const Names &locals) {
    // Only operation-owned natural slots, never labels, codecs or arbitrary
    // user function attributes. Unknown slots retain their original spelling.
    std::string op;
    if (callee.kind == Target::Kind::Operation)
      op = callee.symbol;
    else if (callee.kind == Target::Kind::Declaration &&
             callee.members.empty()) {
      auto selected = bindings.find(callee.symbol);
      if (selected == bindings.end())
        return;
      op = selected->second->application.contract;
    } else
      return;
    for (size_t i = 0; i < atoms.size(); ++i)
      if (naturalAttribute(op, i))
        replaceNatural(atoms[i], locals);
  }
  void statics(std::optional<StaticTerms> &args, const Substitution &sub) {
    if (args)
      for (auto &term : *args)
        close(term, sub);
  }
  // A constant read by a local expression becomes its natural literal.
  bool constant(const Reference &reference) const {
    return reference.target.kind == Target::Kind::Declaration &&
           reference.target.members.empty() &&
           values.count(reference.target.symbol);
  }
  void expression(Expression &e, const Substitution &sub, const Names &locals) {
    if (!tick(e))
      return;
    if (e.kind == Expression::Kind::Name && constant(e.reference)) {
      e.kind = Expression::Kind::Index;
      e.name = std::to_string(values.at(e.reference.target.symbol));
      e.reference = {};
    }
    statics(e.staticArguments, sub);
    if (e.kind == Expression::Kind::Call)
      attributes(e.attributes, e.reference.target, locals);
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
    statics(call.staticArguments, sub);
    if (!call.operatorSymbol)
      attributes(call.attributes, call.callee.target, locals);
    if (call.annotation)
      for (auto &t : *call.annotation)
        type(t, sub);
    if (!call.role || !call.staticArguments ||
        call.callee.target.kind != Target::Kind::Declaration ||
        !call.callee.target.members.empty())
      return;
    auto target = functions.find(call.callee.target.symbol);
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
    Configuration config;
    config.location = call.location;
    config.name = generated(owner, "fn", site);
    if (!declare(config.name, call))
      return;
    config.base = Reference(Target::declaration(f.name));
    for (auto [param, actual] : zip(f.parameters, *call.staticArguments))
      config.arguments.emplace_back(param.name, actual);
    out.configurations.push_back(std::move(config));
    call.callee =
        Reference(Target::declaration(out.configurations.back().name));
    call.staticArguments.reset();
  }
  void body(Body &body, const Substitution &sub, Names locals,
            const Names &parameters, StringRef owner) {
    for (auto &instruction : body) {
      if (!good() || !tick(instruction))
        return;
      if (auto *call = std::get_if<Call>(&instruction.value)) {
        localCall(*call, sub, owner, instruction.site, locals);
        bool constantInput = false;
        for (const auto &input : call->inputs)
          constantInput |= input.steps.empty() && constant(input.root);
        // A flat call reading a constant elaborates as the expression it
        // spells; its occurrence and site stay the authored call's.
        if (constantInput && !call->role) {
          Binding b;
          b.location = call->location;
          b.outputs = call->outputs;
          b.destructure = call->destructure;
          b.annotation = call->annotation;
          b.expression.location = call->location;
          if (call->operatorSymbol) {
            b.expression.kind = Expression::Kind::Operator;
            b.expression.name = *call->operatorSymbol;
          } else {
            b.expression.kind = Expression::Kind::Call;
            b.expression.reference = call->callee;
          }
          b.expression.staticArguments = call->staticArguments;
          b.expression.attributes = call->attributes;
          b.expression.argumentNames = call->argumentNames;
          for (const auto &input : call->inputs)
            b.expression.operands.push_back(syntax::placeExpression(input));
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
        replaceNatural(loop->count, shadowed);
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
                     std::get_if<syntax::Message>(&instruction.value)) {
        locals.insert(message->output);
      } else if (auto *query = std::get_if<syntax::Query>(&instruction.value)) {
        locals.insert(query->outputs.begin(), query->outputs.end());
      }
    }
  }
  void protocolBody(Protocol &p, const Substitution &sub) {
    if (std::holds_alternative<Protocol::MathematicalBody>(p.body) &&
        p.generic) {
      fail(p, "source-mathematical-profile",
           "mathematical protocol requires a closed header in this profile");
      return;
    }
    Names locals, parameters(p.parameters.begin(), p.parameters.end());
    for (const auto &entry : sub)
      locals.insert(entry.first);
    for (auto &arg : p.arguments) {
      type(arg.type, sub);
      locals.insert(arg.name);
    }
    for (auto &result : p.results)
      type(result.type, sub);
    if (auto *instructions = p.instructions())
      body(*instructions, sub, locals, parameters, p.name);
    for (auto &dep : p.dependencies) {
      auto found = protocols.find(symbol(dep.protocol));
      if (!dep.arguments) {
        if (found != protocols.end() && found->second->generic)
          fail(dep, "source-static-required",
               "generic dependency requires explicit domain arguments");
        continue;
      }
      if (found == protocols.end() || !found->second->generic) {
        fail(dep, "source-static-target",
             "specialised dependency requires a generic protocol");
        return;
      }
      auto name = generated(p.name, "dep", dep.name);
      if (!declare(name, dep))
        return;
      specialize(*found->second, name, *dep.arguments, sub, dep);
      dep.protocol = Reference(Target::declaration(name));
      dep.arguments.reset();
    }
  }
  void specialize(const Protocol &definition, StringRef emitted,
                  const StaticAssignments &actuals, const Substitution &outer,
                  const source::Node &node) {
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
    if (!arguments(definition, actuals, outer, sub, node))
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
    Instance result;
    result.location = node.location;
    result.name = generated(entry, "instance", path);
    if (!declare(result.name, node))
      return {};
    result.protocol = Reference(Target::declaration(p.name));
    for (const auto &role : p.roles)
      result.roles.emplace_back(role, role);
    for (const auto &dep : p.dependencies) {
      auto child = selected.find(symbol(dep.protocol));
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
      result.dependencies.emplace_back(
          dep.name, Reference(Target::declaration(instance)));
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
      for (const auto &[name, argument] : config.arguments)
        if (!isDomainRoot(argument.root.value,
                          argument.root.kind == Atom::Kind::String))
          fail(argument.root, "source-static-sort",
               "unknown domain root; use :: for associated members");
      if (!good())
        break;
      auto target = protocols.find(symbol(config.base));
      if (target == protocols.end()) {
        // A definition configuration keeps closed static terms; checking
        // elaborates them against the definition's parameter sorts.
        auto selected = config;
        for (auto &[name, argument] : selected.arguments)
          close(argument, {});
        out.configurations.push_back(std::move(selected));
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
      specialize(*target->second, config.name, config.arguments, {}, config);
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
      if (!entry.arguments)
        continue;
      auto target = protocols.find(symbol(entry.instance));
      if (target == protocols.end() || !target->second->generic) {
        fail(entry, "source-entry-target",
             "entry specialization requires a generic protocol");
        break;
      }
      auto selected = generated(entry.name, "protocol", "root");
      if (!declare(selected, entry))
        break;
      specialize(*target->second, selected, *entry.arguments, {}, entry);
      entry.instance = Reference(Target::declaration(selected));
      entry.arguments.reset();
    }
    std::map<std::string, const Protocol *> selectedProtocols;
    for (const auto &p : out.protocols)
      selectedProtocols.emplace(p.name, &p);
    for (auto &entry : out.entries) {
      auto target = selectedProtocols.find(symbol(entry.instance));
      if (target == selectedProtocols.end())
        continue;
      std::vector<std::string> ancestry;
      entry.instance = Reference(Target::declaration(
          entryInstance(*target->second, entry.name, "root", selectedProtocols,
                        entry, ancestry)));
      if (!good())
        break;
    }
    for (auto &i : out.instances) {
      // Members after the protocol follow dependency aliases of a selected
      // concrete protocol.
      const auto &path = i.protocol.target;
      if (path.kind == Target::Kind::Declaration && !path.members.empty()) {
        if (path.members.size() > maxDepth) {
          fail(i.protocol, "source-staging-limit",
               "instance protocol projection exceeds 64 members");
          break;
        }
        auto selected = selectedProtocols.find(path.symbol);
        for (const auto &member : path.members) {
          if (selected == selectedProtocols.end())
            break;
          const auto &deps = selected->second->dependencies;
          auto dep = llvm::find_if(
              deps, [&](const Dependency &d) { return d.name == member; });
          if (dep == deps.end()) {
            selected = selectedProtocols.end();
            break;
          }
          selected = selectedProtocols.find(symbol(dep->protocol));
        }
        if (selected == selectedProtocols.end()) {
          fail(i.protocol, "source-static-projection",
               "instance projection requires a concrete protocol and declared "
               "dependency aliases");
          break;
        }
        i.protocol = Reference(Target::declaration(selected->second->name));
      }
      auto target = protocols.find(symbol(i.protocol));
      if (target != protocols.end() && target->second->generic)
        fail(i, "source-static-required",
             "instances must name a configured concrete protocol");
      for (auto &[name, parameter] : i.parameters) {
        auto &a = parameter.value;
        if (a.kind != Atom::Kind::Number && !isConstant(a))
          fail(a, "source-constant-reference",
               parameter.ingress
                   ? "ingress bound requires a natural constant"
                   : "instance natural parameter requires a number or bare "
                     "constant");
        replaceNatural(a);
      }
    }
    for (auto &view : out.relationViews) {
      if (!view.height)
        continue;
      replaceNatural(*view.height);
      uint32_t height;
      if (view.height->kind != Atom::Kind::Number ||
          StringRef(view.height->value).getAsInteger(10, height))
        fail(*view.height, "source-constant-reference",
             "relation height requires a bounded natural constant");
    }
    if (!good())
      return std::move(error);
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
