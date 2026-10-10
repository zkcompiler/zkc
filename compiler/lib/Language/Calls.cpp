#include "BodyCheck.h"
#include "zkc/Language/Builtins.h"
#include <algorithm>
#include <numeric>
using namespace llvm;
namespace zkc::language::detail {
std::optional<ValueId> BodyChecker::call(const Expression &expr,
                                         unsigned depth) {
  if (expr.roles) {
    fail("source.call", "role mappings belong to protocol calls", expr.span);
    return {};
  }
  if (expr.text == "index") {
    if (!local() || expr.arguments.size() != 1 || !expr.children.empty() ||
        !expr.staticLabels.empty() || !expr.callLabels.empty()) {
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
    if (!local() || expr.children.size() != 1 || !expr.arguments.empty() ||
        !expr.callLabels.empty()) {
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
  const auto id = uint32_t(&expr - syntax.expressions.data());
  const auto &target = inference->callees.at(id);
  auto &callee = checker.output.declarations[target.declaration.index];
  if (callee.kind == Declaration::Kind::Variant) {
    auto split = StringRef(expr.text).rsplit("::");
    const auto &type = inference->expressions.at(id);
    if (restricted(type) && !checker.types.constructorAllowed(decl, type)) {
      fail("source.private", "variant constructor is restricted", expr.span);
      return {};
    }
    auto alternatives = checker.types.alternatives(type, expr.span);
    if (!alternatives)
      return {};
    auto alt = llvm::find_if(*alternatives,
                             [&](auto &a) { return a.name == split.second; });
    if (alt == alternatives->end() ||
        alt->fields.size() != expr.children.size() ||
        !expr.callLabels.empty()) {
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
    return emit(Construct{std::move(args), alt->name, Construct::Kind::Variant},
                type, {}, expr.span);
  }
  if (callee.kind == Declaration::Kind::Associated) {
    if (!local() || expr.children.size() != 1 || !expr.callLabels.empty()) {
      fail("source.call",
           "associated constructor needs one local representation value",
           expr.span);
      return {};
    }
    const auto &type = inference->expressions.at(id);
    if (type.kind != Type::Kind::Associated) {
      fail("source.call",
           "associated domains have no representation constructor", expr.span);
      return {};
    }
    if (!checker.types.constructorAllowed(decl, type)) {
      fail("source.private", "associated constructor is private", expr.span);
      return {};
    }
    auto fields = checker.types.fields(type, expr.span);
    if (!fields)
      return {};
    auto value =
        expression(expr.children.front(), fields->front().type, depth + 1);
    if (!value || !use(*value, expr.span))
      return {};
    return emit(Construct{{*value}, {}}, type, {}, expr.span);
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
  const auto &staticArgs = inference->arguments.at(id);
  auto subst = checker.types.substitution(callee, staticArgs);
  if (target.component && callee.parent)
    subst.emplace(
        "self:" +
            checker.output.declarations[callee.parent->index].qualifiedName,
        *target.component);
  const auto &binding = inference->inputs.at(id);
  std::vector<ValueId> args(callee.inputs.size());
  for (unsigned i = 0; i < expr.children.size(); ++i) {
    const auto parameter = binding[i];
    auto type = checker.types.substitute(callee.inputs[parameter].type, subst,
                                         expr.span);
    if (!type || (!math() && !checker.types.executableType(*type, expr.span)))
      return {};
    auto arg = expression(expr.children[i], *type, depth + 1);
    if (!arg || !use(*arg, expr.span))
      return {};
    args[parameter] = *arg;
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
      HelperCall{callee.id, std::move(args), staticArgs, target.component, {}},
      *resultType, std::move(resultComponents), expr.span);
  if (result && variable)
    placement->calls.emplace_back(body.operations.size() - 1, *variable);
  return result;
}
std::optional<ValueId> BodyChecker::bulk(const Expression &expr,
                                         unsigned depth) {
  if (!local()) {
    fail("source.mode", "map requires an ordinary local function", expr.span);
    return {};
  }
  const auto id = uint32_t(&expr - syntax.expressions.data());
  const auto &target = inference->callees.at(id);
  const auto &callee = checker.output.declarations[target.declaration.index];
  if (callee.kind != Declaration::Kind::Math || callee.abstract ||
      target.component || callee.outputs.size() != 1 ||
      expr.children.size() != callee.inputs.size() ||
      !llvm::is_contained(expr.each, true)) {
    fail("source.map",
         "map requires a static, defined math fn and at least one each "
         "argument",
         expr.span);
    return {};
  }
  const auto &staticArgs = inference->arguments.at(id);
  auto subst = checker.types.substitution(callee, staticArgs);
  auto field =
      checker.types.substitute(callee.outputs.front().type, subst, expr.span);
  if (!field)
    return {};
  // One scalar field for every helper port; lifting adds only the vectors.
  auto rows = builtinType("vector", {*field});
  if (field->kind != Type::Kind::Field || !rows) {
    if (!rows)
      consumeError(rows.takeError());
    fail("source.map", "mapped helper must return one scalar field", expr.span);
    return {};
  }
  const auto &binding = inference->inputs.at(id);
  std::vector<ValueId> args(callee.inputs.size());
  std::vector<bool> each(args.size());
  for (unsigned i = 0; i < expr.children.size(); ++i) {
    const auto parameter = binding[i];
    auto scalar = checker.types.substitute(callee.inputs[parameter].type, subst,
                                           expr.span);
    if (!scalar)
      return {};
    if (*scalar != *field) {
      fail("source.map", "mapped helper ports must share one scalar field",
           expr.span);
      return {};
    }
    auto expected = expr.each[i] ? *rows : *scalar;
    auto arg = expression(expr.children[i], expected, depth + 1);
    if (!arg || !use(*arg, expr.span))
      return {};
    if (body.values[arg->index].type != expected) {
      fail("source.map", "map argument mode or field differs", expr.span);
      return {};
    }
    args[parameter] = *arg;
    each[parameter] = expr.each[i];
  }
  // Unequal row counts stop this checked application.
  body.mayStop = true;
  return emit(
      BulkApplication{callee.id, std::move(args), staticArgs, std::move(each)},
      *rows, {}, expr.span);
}
} // namespace zkc::language::detail
