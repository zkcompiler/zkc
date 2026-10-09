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
std::optional<ValueId> BodyChecker::call(const Expression &expr,
                                         unsigned depth) {
  if (expr.roles) {
    fail("source.call", "role mappings belong to protocol calls", expr.span);
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
  if (ordered && math()) {
    fail("source.mode", "ordered calls require local or protocol mode",
         expr.span);
    return {};
  }
  if (expr.children.size() != callee.inputs.size()) {
    fail("source.call", "helper argument count mismatch", expr.span);
    return {};
  }
  const auto id = uint32_t(&expr - syntax.expressions.data());
  const auto &staticArgs = inference->arguments.at(id);
  auto subst = checker.types.substitution(callee, staticArgs);
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
    auto arg = expression(expr.children[i], *type, depth + 1);
    if (!arg || !use(*arg, expr.span))
      return {};
    args.push_back(*arg);
  }
  auto resultType =
      checker.types.substitute(callee.outputs.front().type, subst, expr.span);
  if (!resultType)
    return {};
  std::vector<unsigned> dependencies;
  if (!callee.abstract) {
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
  Components resultComponents;
  std::optional<unsigned> variable;
  if (ordered) {
    if (protocol()) {
      auto chosen = placement->owner(expr.span);
      if (!chosen)
        return {};
      resultComponents = std::move(*chosen);
      variable = resultComponents.owners.front();
      for (auto arg : args)
        if (!placement->together(resultComponents, components(arg), expr.span))
          return {};
    }
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
      }
    auto available = substituteDependencies(dependencies);
    if (!available)
      return {};
    resultComponents = *available;
  }
  auto result = emit(
      HelperCall{callee.id, std::move(args), staticArgs, target->second, {}},
      *resultType, std::move(resultComponents), expr.span);
  if (result && variable)
    placement->calls.emplace_back(body.operations.size() - 1, *variable);
  return result;
}
} // namespace zkc::language::detail
