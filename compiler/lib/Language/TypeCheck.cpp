#include "Arguments.h"
#include "Checker.h"
#include "zkc/Language/Builtins.h"
#include "llvm/ADT/StringExtras.h"
#include <algorithm>
#include <limits>
using namespace llvm;
namespace zkc::language::detail {
std::optional<std::vector<Type>>
Checker::arguments(const Declaration &context, const Declaration &target,
                   ArrayRef<SyntaxType> syntax, Span span,
                   ArrayRef<ArgumentLabel> labels) {
  auto binding =
      bindArguments(types, argumentNames<Parameter>(target.parameters),
                    syntax.size(), labels, true, span, "source.generic");
  if (!binding)
    return {};
  std::vector<Type> result(target.parameters.size());
  for (unsigned i = 0; i < syntax.size(); ++i) {
    auto arg = type(context, syntax[i]);
    if (!arg)
      return {};
    result[(*binding)[i]] = std::move(*arg);
  }
  if (formingParameters.count(context.id.index)) {
    for (const auto &argument : result)
      if (!types.chargeType(argument, span))
        return {};
    deferredApplications[context.id.index].push_back({target.id, result, span});
    return result;
  }
  if (!types.checkArguments(target, result, span, &context))
    return {};
  auto bindings = types.substitution(target, result);
  for (const auto &bound : target.bounds)
    if (!types.assumptions(context, bound, bindings, span))
      return {};
  return result;
}

std::optional<Type> Checker::type(const Declaration &context,
                                  const SyntaxType &s, unsigned depth) {
  auto result = elaborateType(context, s, depth);
  if (result && !types.chargeType(*result, s.span))
    return {};
  return result;
}
std::optional<Type> Checker::elaborateType(const Declaration &context,
                                           const SyntaxType &s,
                                           unsigned depth) {
  if (depth > work.limits.typeDepth || !types.charge(1, s.span)) {
    if (!types.diagnostic)
      types.fail("source.limit", "source type complexity limit exceeded",
                 s.span);
    return {};
  }
  using S = SyntaxType::Kind;
  using K = Type::Kind;
  if (s.kind == S::Hole) {
    types.fail("source.inference",
               "a static hole is allowed only as a whole call argument",
               s.span);
    return {};
  }
  if (s.kind == S::Builtin || s.kind == S::Formal) {
    std::vector<Type> arguments;
    for (const auto &syntax : s.arguments) {
      auto argument = elaborateType(context, syntax, depth + 1);
      if (!argument)
        return {};
      arguments.push_back(std::move(*argument));
    }
    auto result = s.kind == S::Formal ? formalType(s.name, arguments)
                                      : builtinType(s.name, arguments);
    if (!result) {
      types.fail(s.kind == S::Formal ? "source.formal" : "source.builtin",
                 toString(result.takeError()), s.span);
      return {};
    }
    return std::move(*result);
  }
  if (s.kind == S::Natural) {
    uint64_t value;
    if (StringRef(s.name).getAsInteger(10, value)) {
      types.fail("source.natural", "natural literal overflows uint64", s.span);
      return {};
    }
    Type result(K::Natural);
    result.dimension = Natural::constant(value);
    return result;
  }
  if (s.kind == S::PowerOfTwo) {
    auto exponent = elaborateType(context, s.arguments[0], depth + 1);
    if (!exponent)
      return {};
    if (exponent->kind != K::Natural) {
      types.fail("source.natural", "pow2 requires a natural exponent", s.span);
      return {};
    }
    auto before = types.naturals.remainingWork();
    auto value = types.naturals.powerOfTwo(exponent->dimension);
    if (!value) {
      types.accept(value.takeError(), s.span);
      return {};
    }
    if (!types.charge(before - types.naturals.remainingWork(), s.span))
      return {};
    Type result(K::Natural);
    result.dimension = std::move(*value);
    result.symbolic = !result.dimension.isClosed();
    return result;
  }
  if (s.kind == S::Add || s.kind == S::Multiply) {
    auto a = elaborateType(context, s.arguments[0], depth + 1),
         b = elaborateType(context, s.arguments[1], depth + 1);
    if (!a || !b)
      return {};
    if (a->kind != K::Natural || b->kind != K::Natural) {
      types.fail("source.natural", "static arithmetic requires naturals",
                 s.span);
      return {};
    }
    auto before = types.naturals.remainingWork();
    auto n = s.kind == S::Add
                 ? types.naturals.add(a->dimension, b->dimension)
                 : types.naturals.multiply(a->dimension, b->dimension);
    if (!n) {
      types.accept(n.takeError(), s.span);
      return {};
    }
    if (!types.charge(before - types.naturals.remainingWork(), s.span))
      return {};
    Type result(K::Natural);
    result.dimension = std::move(*n);
    result.symbolic = !result.dimension.isClosed();
    return result;
  }
  if (s.kind == S::Array) {
    auto element = elaborateType(context, s.arguments[0], depth + 1),
         count = elaborateType(context, s.arguments[1], depth + 1);
    if (!element || !count)
      return {};
    if (!valueType(*element) || count->kind != K::Natural) {
      types.fail("source.type",
                 "array requires an element type and natural length", s.span);
      return {};
    }
    if (count->dimension.isClosed() &&
        count->dimension.closedValue() > work.limits.aggregateLeaves) {
      types.fail("source.limit", "fixed array length exceeds aggregate bound",
                 s.span);
      return {};
    }
    Type result(K::Array);
    result.arguments = {*element};
    result.dimension = count->dimension;
    return result;
  }
  if (s.kind == S::Tuple) {
    Type result(s.arguments.empty() ? K::Unit : K::Tuple);
    for (auto &child : s.arguments) {
      auto t = elaborateType(context, child, depth + 1);
      if (!t)
        return {};
      if (!valueType(*t)) {
        types.fail("source.type", "static term in tuple type", s.span);
        return {};
      }
      result.arguments.push_back(std::move(*t));
    }
    return result;
  }
  if (s.arguments.empty()) {
    if (s.name == "bool")
      return Type{};
    if (s.name == "index")
      return Type(K::Index);
    for (auto &p : context.parameters)
      if (p.name == s.name)
        return parameterType(p);
    auto split = StringRef(s.name).split("::");
    if (!split.second.empty())
      for (auto &p : context.parameters)
        if (p.name == split.first) {
          auto result =
              types.associated(parameterType(p), split.second, s.span);
          return result;
        }
  }
  if (s.arguments.empty()) {
    // Prefer the longest resolvable declaration prefix. Module qualification
    // and a chain of catalog projections use the same source path syntax.
    StringRef prefix = s.name;
    while (prefix.contains("::")) {
      prefix = prefix.rsplit("::").first;
      auto id = resolve(context, prefix, s.span, false);
      if (!id) {
        if (types.diagnostic)
          return {};
        continue;
      }
      const auto &decl = output.declarations[id->index];
      if (decl.kind != Declaration::Kind::Domain &&
          decl.kind != Declaration::Kind::Associated &&
          decl.kind != Declaration::Kind::Alias)
        continue;
      SyntaxType syntax;
      syntax.name = prefix.str();
      syntax.span = s.span;
      auto base = elaborateType(context, syntax, depth + 1);
      if (!base)
        return {};
      return types.associated(
          *base, StringRef(s.name).drop_front(prefix.size() + 2), s.span);
    }
  }
  auto id = resolve(context, s.name, s.span);
  if (!id || !signature(*id, depth + 1))
    return {};
  auto &decl = output.declarations[id->index];
  if (decl.kind == Declaration::Kind::Associated) {
    if (!s.arguments.empty()) {
      types.fail("source.generic",
                 "associated types inherit their component's static arguments",
                 s.span);
      return {};
    }
    auto &parent = output.declarations[decl.parent->index];
    if ((!context.parent || context.parent->index != parent.id.index) &&
        (parent.kind == Declaration::Kind::Interface ||
         !parent.parameters.empty())) {
      types.fail("source.generic", "associated type requires a bound component",
                 s.span);
      return {};
    }
    Type base(K::Component, parent.kind == Declaration::Kind::Interface
                                ? "self:" + parent.qualifiedName
                                : parent.qualifiedName);
    base.symbolic = parent.kind == Declaration::Kind::Interface;
    for (auto &p : parent.parameters)
      base.arguments.push_back(parameterType(p));
    return types.associated(base, decl.name, s.span);
  }
  auto args = arguments(context, decl, s.arguments, s.span, s.labels);
  if (!args)
    return {};
  if (decl.kind == Declaration::Kind::Domain)
    return decl.domain;
  if (decl.kind == Declaration::Kind::Alias)
    return types.substitute(decl.domain, types.substitution(decl, *args),
                            s.span);
  Type result;
  if (decl.kind == Declaration::Kind::Record)
    result.kind = K::Record;
  else if (decl.kind == Declaration::Kind::Variant)
    result.kind = K::Variant;
  else if (decl.kind == Declaration::Kind::Component ||
           decl.kind == Declaration::Kind::Interface)
    result.kind = K::Component;
  else {
    types.fail("source.type", "expected a type, domain, or static component",
               s.span);
    return {};
  }
  result.domain = decl.qualifiedName;
  result.arguments = std::move(*args);
  return result;
}

} // namespace zkc::language::detail
