#include "Checker.h"
#include "zkc/Language/Builtins.h"
#include "llvm/ADT/StringExtras.h"
#include <algorithm>
#include <limits>
using namespace llvm;
namespace zkc::language::detail {
Type parameterType(const Parameter &p) {
  using K = Type::Kind;
  Type value = p.sort == Parameter::Sort::Domain
                   ? domainType(p.domainSort, p.atom)
                   : Type(p.sort == Parameter::Sort::Natural     ? K::Natural
                          : p.sort == Parameter::Sort::Component ? K::Component
                                                                 : K::Parameter,
                          p.atom);
  value.symbolic = true;
  value.assumptions = p.permissions;
  if (p.sort == Parameter::Sort::Natural)
    value.dimension = cantFail(Natural::atom(p.atom));
  if (p.sort == Parameter::Sort::Component)
    value.arguments = p.arguments;
  return value;
}
bool valueType(const Type &type) { return !isStaticOnly(type); }
bool Checker::chargeType(const Type &type, Span span) {
  auto cost =
      typeComplexity(type, work.limits.typeNodes, work.limits.typeDepth);
  if (!cost)
    return accept(cost.takeError());
  return charge(*cost, span);
}
const Parameter *Checker::parameter(StringRef atom) const {
  auto found = parameters.find(atom.str());
  if (found == parameters.end())
    return nullptr;
  auto [id, index] = found->second;
  return &output.declarations[id.index].parameters[index];
}
const Declaration *Checker::typeDeclaration(const Type &type) const {
  using K = Type::Kind;
  if (type.kind != K::Record && type.kind != K::Variant &&
      type.kind != K::Associated && type.kind != K::Component)
    return nullptr;
  auto found = qualified.find(type.domain);
  return found == qualified.end() ? nullptr
                                  : &output.declarations[found->second.index];
}
bool Checker::symbolic(const Type &type) const {
  return type.symbolic || !type.dimension.isClosed() ||
         llvm::any_of(type.arguments, [&](auto &t) { return symbolic(t); });
}
Substitution Checker::substitution(const Declaration &decl,
                                   ArrayRef<Type> args) const {
  Substitution out;
  for (unsigned i = 0; i < args.size() && i < decl.parameters.size(); ++i)
    out.emplace(decl.parameters[i].atom, args[i]);
  return out;
}
std::optional<Type> Checker::substitute(const Type &input,
                                        const Substitution &bindings, Span span,
                                        unsigned depth) {
  if (depth > work.limits.typeDepth || !charge(1, span)) {
    if (!diagnostic)
      fail("source.limit", "type substitution depth limit", span);
    return {};
  }
  if (input.symbolic) {
    auto found = bindings.find(input.domain);
    if (found != bindings.end()) {
      if (!chargeType(found->second, span))
        return {};
      return found->second;
    }
  }
  if (!chargeType(input, span))
    return {};
  Type result = input;
  for (auto &arg : result.arguments) {
    auto t = substitute(arg, bindings, span, depth + 1);
    if (!t)
      return {};
    arg = std::move(*t);
  }
  if (!result.dimension.isClosed()) {
    auto before = naturals.remainingWork();
    auto n = naturals.substitute(
        result.dimension, [&](StringRef name) -> const Natural * {
          auto found = bindings.find(name.str());
          return found != bindings.end() &&
                         found->second.kind == Type::Kind::Natural
                     ? &found->second.dimension
                     : nullptr;
        });
    if (!n) {
      accept(n.takeError());
      return {};
    }
    if (!charge(before - naturals.remainingWork(), span))
      return {};
    result.dimension = std::move(*n);
    if (result.kind == Type::Kind::Natural) {
      result.symbolic = !result.dimension.isClosed();
      if (!result.symbolic)
        result.domain.clear();
    }
  }
  if ((result.kind == Type::Kind::Associated || !domainSort(result).empty()) &&
      !result.arguments.empty()) {
    StringRef name = result.domain;
    auto pos = name.rfind("::");
    return associated(result.arguments.front(), name.drop_front(pos + 2), span);
  }
  return result;
}
std::optional<Type> Checker::associated(const Type &base, StringRef member,
                                        Span span) {
  if (!chargeType(base, span))
    return {};
  if (member.contains("::")) {
    Type current = base;
    unsigned depth = 0;
    while (!member.empty()) {
      if (++depth > work.limits.typeDepth) {
        fail("source.limit", "associated path depth limit", span);
        return {};
      }
      auto [head, tail] = member.split("::");
      auto next = associated(current, head, span);
      if (!next)
        return {};
      current = std::move(*next);
      member = tail;
    }
    return current;
  }
  if (!domainSort(base).empty()) {
    auto result = domainMember(base, member);
    if (!result) {
      fail("source.type", toString(result.takeError()), span);
      return {};
    }
    return std::move(*result);
  }
  if (base.kind != Type::Kind::Component) {
    fail("source.type", "associated member requires a component or domain",
         span);
    return {};
  }
  const Declaration *owner = nullptr;
  if (base.symbolic) {
    if (auto p = parameter(base.domain); p && p->interface)
      owner = &output.declarations[p->interface->index];
    else if (StringRef(base.domain).starts_with("self:")) {
      auto found = qualified.find(base.domain.substr(5));
      if (found != qualified.end())
        owner = &output.declarations[found->second.index];
    }
  } else
    owner = typeDeclaration(base);
  if (!owner) {
    fail("source.type", "unknown associated component", span);
    return {};
  }
  for (auto id : owner->members) {
    auto &decl = output.declarations[id.index];
    if (decl.name != member)
      continue;
    if (decl.kind != Declaration::Kind::Associated || !signature(id)) {
      if (!diagnostic)
        fail("source.type", "member is not a type", span);
      return {};
    }
    Type result(Type::Kind::Associated, decl.qualifiedName);
    result.arguments = {base};
    result.assumptions = decl.permissions.value_or(Permissions{});
    if (isDomainSort(decl.associatedSort)) {
      if (!decl.abstract)
        return substitute(decl.domain, substitution(*owner, base.arguments),
                          span);
      auto domain = domainType(decl.associatedSort, decl.qualifiedName);
      domain.arguments = {base};
      domain.assumptions = result.assumptions;
      result = std::move(domain);
      result.symbolic = true;
    }
    return result;
  }
  fail("source.type", "unknown associated type: " + member, span);
  return {};
}
std::optional<std::vector<Type>> Checker::arguments(const Declaration &context,
                                                    const Declaration &target,
                                                    ArrayRef<SyntaxType> syntax,
                                                    Span span) {
  if (syntax.size() != target.parameters.size()) {
    fail("source.generic", "static argument count differs", span);
    return {};
  }
  std::vector<Type> result;
  for (auto &s : syntax) {
    auto arg = type(context, s);
    if (!arg)
      return {};
    result.push_back(std::move(*arg));
  }
  if (formingParameters.count(context.id.index)) {
    for (const auto &argument : result)
      if (!chargeType(argument, span))
        return {};
    deferredApplications[context.id.index].push_back({target.id, result, span});
    return result;
  }
  if (!checkArguments(target, result, span, &context))
    return {};
  auto bindings = substitution(target, result);
  for (const auto &bound : target.bounds)
    if (!assumptions(context, bound, bindings, span))
      return {};
  return result;
}
bool Checker::checkArguments(const Declaration &target, ArrayRef<Type> args,
                             Span span, const Declaration *context,
                             const Substitution &extra) {
  if (args.size() != target.parameters.size())
    return fail("source.generic", "static argument count differs", span);
  auto subst = substitution(target, args);
  subst.insert(extra.begin(), extra.end());
  for (unsigned i = 0; i < args.size(); ++i) {
    auto &p = target.parameters[i];
    auto &a = args[i];
    bool kind = false;
    switch (p.sort) {
    case Parameter::Sort::Domain:
      kind = domainSort(a) == p.domainSort;
      break;
    case Parameter::Sort::Natural:
      kind = a.kind == Type::Kind::Natural;
      break;
    case Parameter::Sort::Type:
      kind = valueType(a);
      if (kind && !executableType(a, span))
        return false;
      break;
    case Parameter::Sort::Component: {
      kind = a.kind == Type::Kind::Component;
      if (!kind)
        break;
      const Declaration *actual = nullptr;
      std::vector<Type> actualArgs;
      if (a.symbolic) {
        auto param = parameter(a.domain);
        if (param && param->interface) {
          actual = &output.declarations[param->interface->index];
          actualArgs = param->arguments;
        }
      } else {
        auto component = typeDeclaration(a);
        if (component && component->implementation) {
          auto selected =
              substitute(*component->implementation,
                         substitution(*component, a.arguments), span);
          if (!selected)
            return false;
          actual = typeDeclaration(*selected);
          actualArgs = selected->arguments;
        }
      }
      if (!actual || !p.interface || actual->id.index != p.interface->index)
        return fail("source.conformance",
                    "component does not implement required interface", span);
      if (actualArgs.size() != p.arguments.size())
        return fail("source.conformance", "interface static arguments differ",
                    span);
      for (unsigned j = 0; j < p.arguments.size(); ++j) {
        auto expected = substitute(p.arguments[j], subst, span);
        if (!expected)
          return false;
        if (*expected != actualArgs[j])
          return fail("source.conformance", "interface static arguments differ",
                      span);
      }
      break;
    }
    }
    if (!kind)
      return fail("source.generic", "static argument has wrong sort", span);
    if (valueType(a)) {
      auto caps = permissions(a, span, context);
      if (!caps)
        return false;
      if (!caps->includes(p.permissions))
        return fail("source.permission",
                    "static argument lacks required permission", span);
    }
  }
  for (const auto &bound : target.capabilityBounds) {
    CapabilityBound goal{bound.predicate, {}, span};
    for (const auto &argument : bound.arguments) {
      auto actual = substitute(argument, subst, span);
      if (!actual)
        return false;
      goal.arguments.push_back(std::move(*actual));
    }
    if (!entails(context, goal))
      return false;
  }
  for (const auto &bound : target.permissionBounds) {
    Type requirement = bound.type;
    requirement.assumptions = {};
    auto actual = substitute(requirement, subst, span);
    if (!actual)
      return false;
    auto caps = permissions(*actual, span, context);
    if (!caps)
      return false;
    if (!caps->includes(bound.permissions))
      return fail("source.permission",
                  "associated type lacks required permission", span);
  }
  for (auto &bound : target.bounds) {
    Type lhs(Type::Kind::Natural), rhs(Type::Kind::Natural);
    lhs.dimension = bound.lhs;
    rhs.dimension = bound.rhs;
    auto l = substitute(lhs, subst, span), r = substitute(rhs, subst, span);
    if (!l || !r)
      return false;
    if (l->dimension.isClosed() && r->dimension.isClosed() &&
        l->dimension.closedValue() > r->dimension.closedValue())
      return fail("source.bound", "closed natural requirement does not hold",
                  span);
  }
  return true;
}
std::optional<Type> Checker::type(const Declaration &context,
                                  const SyntaxType &s, unsigned depth) {
  if (depth > work.limits.typeDepth || ++typeNodes > work.limits.typeNodes ||
      !charge(1, s.span)) {
    if (!diagnostic)
      fail("source.limit", "source type complexity limit exceeded", s.span);
    return {};
  }
  using S = SyntaxType::Kind;
  using K = Type::Kind;
  if (s.kind == S::Builtin || s.kind == S::Formal) {
    std::vector<Type> arguments;
    for (const auto &syntax : s.arguments) {
      auto argument = type(context, syntax, depth + 1);
      if (!argument)
        return {};
      arguments.push_back(std::move(*argument));
    }
    auto result = s.kind == S::Formal ? formalType(s.name, arguments)
                                      : builtinType(s.name, arguments);
    if (!result) {
      fail(s.kind == S::Formal ? "source.formal" : "source.builtin",
           toString(result.takeError()), s.span);
      return {};
    }
    return std::move(*result);
  }
  if (s.kind == S::Natural) {
    uint64_t value;
    if (StringRef(s.name).getAsInteger(10, value)) {
      fail("source.natural", "natural literal overflows uint64", s.span);
      return {};
    }
    Type result(K::Natural);
    result.dimension = Natural::constant(value);
    return result;
  }
  if (s.kind == S::PowerOfTwo) {
    auto exponent = type(context, s.arguments[0], depth + 1);
    if (!exponent)
      return {};
    if (exponent->kind != K::Natural) {
      fail("source.natural", "pow2 requires a natural exponent", s.span);
      return {};
    }
    auto before = naturals.remainingWork();
    auto value = naturals.powerOfTwo(exponent->dimension);
    if (!value) {
      accept(value.takeError());
      return {};
    }
    if (!charge(before - naturals.remainingWork(), s.span))
      return {};
    Type result(K::Natural);
    result.dimension = std::move(*value);
    result.symbolic = !result.dimension.isClosed();
    return result;
  }
  if (s.kind == S::Add || s.kind == S::Multiply) {
    auto a = type(context, s.arguments[0], depth + 1),
         b = type(context, s.arguments[1], depth + 1);
    if (!a || !b)
      return {};
    if (a->kind != K::Natural || b->kind != K::Natural) {
      fail("source.natural", "static arithmetic requires naturals", s.span);
      return {};
    }
    auto before = naturals.remainingWork();
    auto n = s.kind == S::Add ? naturals.add(a->dimension, b->dimension)
                              : naturals.multiply(a->dimension, b->dimension);
    if (!n) {
      accept(n.takeError());
      return {};
    }
    if (!charge(before - naturals.remainingWork(), s.span))
      return {};
    Type result(K::Natural);
    result.dimension = std::move(*n);
    result.symbolic = !result.dimension.isClosed();
    return result;
  }
  if (s.kind == S::Array) {
    auto element = type(context, s.arguments[0], depth + 1),
         count = type(context, s.arguments[1], depth + 1);
    if (!element || !count)
      return {};
    if (!valueType(*element) || count->kind != K::Natural) {
      fail("source.type", "array requires an element type and natural length",
           s.span);
      return {};
    }
    if (count->dimension.isClosed() &&
        count->dimension.closedValue() > work.limits.aggregateLeaves) {
      fail("source.limit", "fixed array length exceeds aggregate bound",
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
      auto t = type(context, child, depth + 1);
      if (!t)
        return {};
      if (!valueType(*t)) {
        fail("source.type", "static term in tuple type", s.span);
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
          auto result = associated(parameterType(p), split.second, s.span);
          return result;
        }
  }
  if (s.arguments.empty()) {
    // Prefer the longest resolvable declaration prefix. Module qualification
    // and a chain of catalog projections use the same source path syntax.
    StringRef prefix = s.name;
    while (prefix.contains("::")) {
      prefix = prefix.rsplit("::").first;
      auto previous = diagnostic;
      auto id = resolve(context, prefix, s.span);
      diagnostic = std::move(previous);
      if (!id)
        continue;
      const auto &decl = output.declarations[id->index];
      if (decl.kind != Declaration::Kind::Domain &&
          decl.kind != Declaration::Kind::Associated &&
          decl.kind != Declaration::Kind::Alias)
        continue;
      SyntaxType syntax;
      syntax.name = prefix.str();
      syntax.span = s.span;
      auto base = type(context, syntax, depth + 1);
      if (!base)
        return {};
      return associated(*base, StringRef(s.name).drop_front(prefix.size() + 2),
                        s.span);
    }
  }
  auto id = resolve(context, s.name, s.span);
  if (!id || !signature(*id, depth + 1))
    return {};
  auto &decl = output.declarations[id->index];
  if (decl.kind == Declaration::Kind::Associated) {
    auto &parent = output.declarations[decl.parent->index];
    if ((!context.parent || context.parent->index != parent.id.index) &&
        (parent.kind == Declaration::Kind::Interface ||
         !parent.parameters.empty())) {
      fail("source.generic", "associated type requires a bound component",
           s.span);
      return {};
    }
    Type base(K::Component, parent.kind == Declaration::Kind::Interface
                                ? "self:" + parent.qualifiedName
                                : parent.qualifiedName);
    base.symbolic = parent.kind == Declaration::Kind::Interface;
    for (auto &p : parent.parameters)
      base.arguments.push_back(parameterType(p));
    return associated(base, decl.name, s.span);
  }
  auto args = arguments(context, decl, s.arguments, s.span);
  if (!args)
    return {};
  if (decl.kind == Declaration::Kind::Domain)
    return decl.domain;
  if (decl.kind == Declaration::Kind::Alias)
    return substitute(decl.domain, substitution(decl, *args), s.span);
  Type result;
  if (decl.kind == Declaration::Kind::Record)
    result.kind = K::Record;
  else if (decl.kind == Declaration::Kind::Variant)
    result.kind = K::Variant;
  else if (decl.kind == Declaration::Kind::Component ||
           decl.kind == Declaration::Kind::Interface)
    result.kind = K::Component;
  else {
    fail("source.type", "expected a type, domain, or static component", s.span);
    return {};
  }
  result.domain = decl.qualifiedName;
  result.arguments = std::move(*args);
  return result;
}
bool Checker::assumptions(const Declaration &caller, const NaturalBound &bound,
                          const Substitution &bindings, Span span) {
  Type lhs(Type::Kind::Natural), rhs(Type::Kind::Natural);
  lhs.dimension = bound.lhs;
  rhs.dimension = bound.rhs;
  auto l = substitute(lhs, bindings, span), r = substitute(rhs, bindings, span);
  if (!l || !r)
    return false;
  if (l->dimension.isClosed() && r->dimension.isClosed())
    return l->dimension.closedValue() <= r->dimension.closedValue() ||
           fail("source.bound", "natural requirement is false", span);
  if (l->dimension == r->dimension)
    return true;
  for (auto &given : caller.bounds) {
    if (!charge(1, span))
      return false;
    if (given.rhs == r->dimension &&
        (given.lhs == l->dimension ||
         (given.lhs.isClosed() && l->dimension.isClosed() &&
          given.lhs.closedValue() >= l->dimension.closedValue())))
      return true;
  }
  return fail("source.bound", "generic call needs an explicit natural bound",
              span);
}
} // namespace zkc::language::detail
