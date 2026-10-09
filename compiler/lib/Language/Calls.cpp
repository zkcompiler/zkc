#include "BodyCheck.h"
#include <algorithm>
#include <numeric>
using namespace llvm;
namespace zkc::language::detail {
std::optional<std::pair<DeclarationId, std::optional<Type>>>
BodyChecker::callable(const Expression &expr) {
  auto parts = StringRef(expr.text).split("::");
  if (!parts.second.empty())
    for (auto &parameter : decl.parameters) {
      if (parameter.name != parts.first || !parameter.interface)
        continue;
      SyntaxType term;
      term.name = parameter.name;
      term.span = expr.span;
      auto component = checker.type(decl, term);
      if (!component)
        return {};
      auto &interface = checker.output.declarations[parameter.interface->index];
      for (auto id : interface.members)
        if (checker.output.declarations[id.index].name == parts.second)
          return std::make_pair(id, std::optional<Type>(*component));
      fail("source.call", "unknown interface member", expr.span);
      return {};
    }
  auto id = checker.resolve(decl, expr.text, expr.span);
  if (!id)
    return {};
  if (checker.output.declarations[id->index].abstract &&
      checker.output.declarations[id->index].kind !=
          Declaration::Kind::Associated) {
    fail("source.call", "abstract call requires a bound component", expr.span);
    return {};
  }
  return std::make_pair(*id, std::optional<Type>{});
}
bool BodyChecker::infer(const Type &pattern, const Type &actual,
                        Substitution &bindings, Span span) {
  if (!checker.types.charge(1, span))
    return false;
  if (pattern.symbolic && pattern.kind != Type::Kind::Associated) {
    // Only a bare parameter is inferred. Associations and natural equations do
    // not have unique inverses and are never solved here.
    auto *parameter = checker.types.parameter(pattern.domain);
    if (parameter &&
        (pattern.kind != Type::Kind::Natural ||
         pattern.dimension == cantFail(Natural::atom(pattern.domain)))) {
      auto [it, inserted] = bindings.emplace(pattern.domain, actual);
      return inserted || it->second == actual ||
             fail("source.inference", "conflicting static argument inference",
                  span);
    }
  }
  if (pattern.kind == actual.kind && pattern.domain == actual.domain &&
      pattern.arguments.size() == actual.arguments.size()) {
    for (unsigned i = 0; i < pattern.arguments.size(); ++i)
      if (!infer(pattern.arguments[i], actual.arguments[i], bindings, span))
        return false;
    if (pattern.kind == Type::Kind::Array && !pattern.dimension.isClosed()) {
      for (auto &[factors, coefficient] : pattern.dimension.terms())
        if (pattern.dimension.terms().size() == 1 && coefficient == 1 &&
            factors.size() == 1 &&
            factors.front().kind == Natural::Factor::Kind::Atom) {
          Type p(Type::Kind::Natural, factors.front().name);
          p.symbolic = true;
          p.dimension = pattern.dimension;
          Type a(Type::Kind::Natural);
          a.dimension = actual.dimension;
          a.symbolic = !a.dimension.isClosed();
          if (!infer(p, a, bindings, span))
            return false;
        }
    }
  }
  return true;
}
std::optional<std::vector<Type>>
BodyChecker::actuals(const Declaration &callee, const Expression &expr,
                     ArrayRef<std::optional<Type>> inputs,
                     std::optional<Type> expected,
                     std::optional<Type> component) {
  Substitution bindings;
  if (component && callee.parent) {
    auto &interface = checker.output.declarations[callee.parent->index];
    bindings = checker.types.substitution(interface, component->arguments);
    bindings.emplace("self:" + interface.qualifiedName, *component);
  }
  unsigned inherited =
      component && callee.parent
          ? checker.output.declarations[callee.parent->index].parameters.size()
          : 0;
  if (!expr.arguments.empty()) {
    if (expr.arguments.size() + inherited != callee.parameters.size()) {
      fail("source.generic", "static argument count differs", expr.span);
      return {};
    }
    for (unsigned i = 0; i < expr.arguments.size(); ++i) {
      auto t = checker.type(decl, expr.arguments[i]);
      if (!t)
        return {};
      bindings.emplace(callee.parameters[inherited + i].atom, *t);
    }
  } else {
    for (unsigned i = 0; i < inputs.size() && i < callee.inputs.size(); ++i)
      if (inputs[i] &&
          !infer(callee.inputs[i].type, *inputs[i], bindings, expr.span))
        return {};
    if (expected && callee.outputs.size() == 1 &&
        !infer(callee.outputs.front().type, *expected, bindings, expr.span))
      return {};
  }
  std::vector<Type> result;
  for (auto &p : callee.parameters) {
    auto it = bindings.find(p.atom);
    if (it == bindings.end()) {
      fail("source.inference", "static argument cannot be inferred: " + p.name,
           expr.span);
      return {};
    }
    result.push_back(it->second);
  }
  if (!checker.types.checkArguments(callee, result, expr.span, &decl, bindings))
    return {};
  for (auto &bound : callee.bounds)
    if (!checker.types.assumptions(decl, bound, bindings, expr.span))
      return {};
  return result;
}
std::optional<ValueId> BodyChecker::call(const Expression &expr,
                                         std::optional<Type> expected,
                                         unsigned depth) {
  if (expr.roles || !expr.services.empty()) {
    fail("source.call",
         "role mappings and managed arguments belong to protocol calls",
         expr.span);
    return {};
  }
  if (expr.text == "index") {
    if (!local() || expr.arguments.size() != 1 || !expr.children.empty()) {
      fail("source.call",
           "index<N>() requires one static natural in local mode", expr.span);
      return {};
    }
    auto value = checker.type(decl, expr.arguments.front());
    if (!value)
      return {};
    if (value->kind != Type::Kind::Natural) {
      fail("source.type", "index<N>() requires a natural", expr.span);
      return {};
    }
    return emit(LocalPrimitive{"index.constant", {}, {}, {*value}},
                Type(Type::Kind::Index), {}, expr.span);
  }
  if (expr.text == "unpack") {
    if (!local() || expr.children.size() != 1 || !expr.arguments.empty()) {
      fail("source.call", "unpack requires one local value", expr.span);
      return {};
    }
    auto value = expression(expr.children.front(), {}, depth + 1);
    if (!value)
      return {};
    auto source = body.values[value->index].type;
    if (!checker.types.constructorAllowed(decl, source)) {
      fail("source.private", "unpack requires constructor authority",
           expr.span);
      return {};
    }
    if (source.kind == Type::Kind::Variant) {
      fail("source.type", "variants are unpacked by exhaustive match",
           expr.span);
      return {};
    }
    auto fields = checker.types.fields(source, expr.span);
    if (!fields)
      return {};
    Type result(fields->empty() ? Type::Kind::Unit : Type::Kind::Tuple);
    for (auto &f : *fields)
      result.arguments.push_back(f.type);
    if (source.kind == Type::Kind::Associated)
      result = fields->front().type;
    if (!use(*value, expr.span))
      return {};
    // The empty alternative denotes product construction; unpack is explicit
    // because it consumes a restricted wrapper's custody token in lowering.
    return emit(Construct{{*value}, {}, Construct::Kind::Unpack}, result, {},
                expr.span);
  }
  // Enum alternative constructors resolve the nominal type before its label.
  auto split = StringRef(expr.text).rsplit("::");
  if (!split.second.empty()) {
    bool parameterMember = false;
    for (auto &p : decl.parameters)
      parameterMember |= p.name == split.first;
    if (!parameterMember) {
      auto saved = checker.types.diagnostic;
      auto id = checker.resolve(decl, split.first, expr.span);
      if (!id)
        checker.types.diagnostic = saved;
      else if (checker.output.declarations[id->index].kind ==
               Declaration::Kind::Variant) {
        SyntaxType term;
        term.name = split.first.str();
        term.arguments = expr.arguments;
        term.span = expr.span;
        auto type = checker.type(decl, term);
        if (!type)
          return {};
        if (restricted(*type) &&
            !checker.types.constructorAllowed(decl, *type)) {
          fail("source.private", "variant constructor is restricted",
               expr.span);
          return {};
        }
        auto alternatives = checker.types.alternatives(*type, expr.span);
        if (!alternatives)
          return {};
        auto alt = llvm::find_if(
            *alternatives, [&](auto &a) { return a.name == split.second; });
        if (alt == alternatives->end() ||
            alt->fields.size() != expr.children.size()) {
          fail("source.call", "unknown alternative or wrong payload count",
               expr.span);
          return {};
        }
        if (!local()) {
          fail("source.mode", "variant construction requires local mode",
               expr.span);
          return {};
        }
        std::vector<ValueId> args;
        for (unsigned i = 0; i < expr.children.size(); ++i) {
          auto v = expression(expr.children[i], alt->fields[i].type, depth + 1);
          if (!v || !use(*v, expr.span))
            return {};
          args.push_back(*v);
        }
        return emit(
            Construct{std::move(args), alt->name, Construct::Kind::Variant},
            *type, {}, expr.span);
      }
    }
  }
  auto target = callable(expr);
  if (!target)
    return {};
  auto &callee = checker.output.declarations[target->first.index];
  if (callee.kind == Declaration::Kind::Associated) {
    if (!local() || expr.children.size() != 1) {
      fail("source.call",
           "associated constructor needs one local representation value",
           expr.span);
      return {};
    }
    SyntaxType term;
    term.name = expr.text;
    term.arguments = expr.arguments;
    term.span = expr.span;
    auto type = checker.type(decl, term);
    if (!type)
      return {};
    if (type->kind != Type::Kind::Associated) {
      fail("source.call",
           "associated domains have no representation constructor", expr.span);
      return {};
    }
    if (!checker.types.constructorAllowed(decl, *type)) {
      fail("source.private", "associated constructor is private", expr.span);
      return {};
    }
    auto fields = checker.types.fields(*type, expr.span);
    if (!fields)
      return {};
    auto value =
        expression(expr.children.front(), fields->front().type, depth + 1);
    if (!value || !use(*value, expr.span))
      return {};
    return emit(Construct{{*value}, {}}, *type, {}, expr.span);
  }
  if (callee.kind != Declaration::Kind::Math &&
      callee.kind != Declaration::Kind::Local) {
    fail("source.call", "expected a mathematical or local helper", expr.span);
    return {};
  }
  bool ordered = callee.kind == Declaration::Kind::Local;
  if (!ordered)
    owner.reset();
  if ((ordered && math()) || (ordered && protocol() && !owner)) {
    fail("source.mode",
         "ordered protocol calls require a whole binding or assignment RHS at "
         "an explicit singleton owner",
         expr.span);
    return {};
  }
  if (expr.children.size() != callee.inputs.size()) {
    fail("source.call", "helper argument count mismatch", expr.span);
    return {};
  }
  std::vector<std::optional<Type>> hints;
  for (auto child : expr.children) {
    hints.push_back(hint(child, depth + 1));
    if (checker.types.diagnostic)
      return {};
  }
  auto staticArgs = actuals(callee, expr, hints, expected, target->second);
  if (!staticArgs)
    return {};
  auto subst = checker.types.substitution(callee, *staticArgs);
  if (target->second && callee.parent)
    subst.emplace(
        "self:" +
            checker.output.declarations[callee.parent->index].qualifiedName,
        *target->second);
  std::vector<ValueId> args;
  for (unsigned i = 0; i < expr.children.size(); ++i) {
    auto type =
        checker.types.substitute(callee.inputs[i].type, subst, expr.span);
    if (!type || (!math() && !checker.types.executableType(*type, expr.span)))
      return {};
    auto selectedOwner = owner;
    owner.reset();
    auto arg = expression(expr.children[i], *type, depth + 1);
    owner = selectedOwner;
    if (!arg || !use(*arg, expr.span))
      return {};
    if (owner &&
        !llvm::is_contained(body.values[arg->index].components, *owner)) {
      fail("source.roles", "local argument is unavailable at its owner",
           expr.span);
      return {};
    }
    if (owner && body.values[arg->index].components.size() > 1) {
      auto p = checker.types.permissions(*type, expr.span, &decl);
      if (!p || !p->copy || !p->drop) {
        if (!checker.types.diagnostic)
          fail("source.permission",
               "owned call cannot duplicate or discard restricted components",
               expr.span);
        return {};
      }
    }
    args.push_back(*arg);
  }
  auto resultType =
      checker.types.substitute(callee.outputs.front().type, subst, expr.span);
  if (!resultType)
    return {};
  std::vector<unsigned> dependencies;
  if (!callee.abstract) {
    if (!checker.body(callee.id, callDepth + 1))
      return {};
    checker.bodyHeights[decl.id.index] =
        std::max(checker.bodyHeights[decl.id.index],
                 checker.bodyHeights[callee.id.index] + 1);
    if (callee.kind == Declaration::Kind::Math)
      dependencies =
          callee.body->values[callee.body->results.front().index].components;
    body.mayStop |= callee.body->mayStop;
    body.opaque |= callee.body->opaque;
  } else {
    dependencies.resize(args.size());
    std::iota(dependencies.begin(), dependencies.end(), 0);
    auto effects = callee.effectAllowance.value_or(Effects{ordered, ordered});
    body.mayStop |= effects.mayStop;
    body.opaque |= effects.opaque;
  }
  std::vector<unsigned> components;
  if (ordered) {
    if (owner)
      components = {*owner};
  } else {
    auto substituteDependencies = [&](ArrayRef<unsigned> indices) {
      std::vector<ValueId> selected;
      for (auto i : indices)
        selected.push_back(args[i]);
      return combine(selected, expr.span);
    };
    if (callee.body)
      for (auto &requirement : callee.body->formationRequirements) {
        auto required = substituteDependencies(requirement);
        if (!required)
          return std::optional<ValueId>{};
        if (math() && !required->empty())
          body.formationRequirements.push_back(*required);
      }
    auto available = substituteDependencies(dependencies);
    if (!available)
      return {};
    components = *available;
    if (math() && callee.abstract && !components.empty())
      body.formationRequirements.push_back(components);
  }
  return emit(HelperCall{callee.id, std::move(args), std::move(*staticArgs),
                         target->second, owner},
              *resultType, std::move(components), expr.span);
}
} // namespace zkc::language::detail
