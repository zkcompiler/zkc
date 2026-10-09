#include "Semantics.h"
#include "zkc/Language/Builtins.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/ScopeExit.h"
using namespace llvm;
namespace zkc::language::detail {
Semantics::Semantics(const std::vector<Declaration> &declarations, Work &work,
                     std::function<bool(DeclarationId)> complete)
    : work(work), naturals(work.limits.work, work.limits.naturalTerms,
                           work.limits.naturalFactors),
      declarations(declarations), complete(std::move(complete)) {
  for (const auto &decl : declarations) {
    indexDeclaration(decl);
    for (unsigned i = 0; i < decl.parameters.size(); ++i)
      indexParameter(decl.parameters[i], decl.id, i);
  }
}
void Semantics::indexDeclaration(const Declaration &decl) {
  if (!decl.origin && !decl.anonymous)
    qualified.emplace(decl.qualifiedName, decl.id);
}
void Semantics::indexParameter(const Parameter &parameter, DeclarationId id,
                               unsigned index) {
  parameters.emplace(parameter.atom, std::make_pair(id, index));
}
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

bool Semantics::fail(StringRef code, const Twine &message, Span span,
                     std::vector<Span> related) {
  if (!diagnostic)
    diagnostic =
        Diagnostic{code.str(), message.str(), span, std::move(related)};
  return false;
}
bool Semantics::accept(Error error, std::optional<Span> fallback) {
  auto found = diagnose(std::move(error), fallback);
  if (!found)
    return true;
  if (!diagnostic)
    diagnostic = std::move(found);
  return false;
}
bool Semantics::charge(uint64_t count, Span span) {
  return accept(work.charge(count, span));
}
Error Semantics::takeError() {
  assert(diagnostic && "failed semantic query must carry a diagnostic");
  auto result = make_error<DiagnosticError>(std::move(*diagnostic));
  diagnostic.reset();
  return result;
}
bool valueType(const Type &type) { return !isStaticOnly(type); }
bool Semantics::chargeType(const Type &type, Span span) {
  auto cost =
      typeComplexity(type, work.limits.typeNodes, work.limits.typeDepth);
  if (!cost)
    return accept(cost.takeError(), span);
  return charge(*cost, span);
}
const Parameter *Semantics::parameter(StringRef atom) const {
  auto found = parameters.find(atom.str());
  if (found == parameters.end())
    return nullptr;
  auto [id, index] = found->second;
  return &declarations[id.index].parameters[index];
}
const Declaration *Semantics::typeDeclaration(const Type &type) const {
  using K = Type::Kind;
  if (type.kind != K::Record && type.kind != K::Variant &&
      type.kind != K::Associated && type.kind != K::Component)
    return nullptr;
  auto found = qualified.find(type.domain);
  return found == qualified.end() ? nullptr
                                  : &declarations[found->second.index];
}
bool Semantics::symbolic(const Type &type) const {
  return type.symbolic || !type.dimension.isClosed() ||
         llvm::any_of(type.arguments, [&](auto &t) { return symbolic(t); });
}
Substitution Semantics::substitution(const Declaration &decl,
                                     ArrayRef<Type> args) const {
  Substitution out;
  for (unsigned i = 0; i < args.size() && i < decl.parameters.size(); ++i)
    out.emplace(decl.parameters[i].atom, args[i]);
  return out;
}
std::optional<Type> Semantics::substitute(const Type &input,
                                          const Substitution &bindings,
                                          Span span, unsigned depth) {
  if (normalizationDepth >= work.limits.typeDepth) {
    fail("source.limit", "type normalization depth limit", span);
    return {};
  }
  ++normalizationDepth;
  auto restoreDepth = llvm::scope_exit([&] { --normalizationDepth; });

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
      accept(n.takeError(), span);
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
std::optional<Type> Semantics::associated(const Type &base, StringRef member,
                                          Span span) {
  if (normalizationDepth >= work.limits.typeDepth) {
    fail("source.limit", "type normalization depth limit", span);
    return {};
  }
  ++normalizationDepth;
  auto restoreDepth = llvm::scope_exit([&] { --normalizationDepth; });

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
      owner = &declarations[p->interface->index];
    else if (StringRef(base.domain).starts_with("self:")) {
      auto found = qualified.find(base.domain.substr(5));
      if (found != qualified.end())
        owner = &declarations[found->second.index];
    }
  } else
    owner = typeDeclaration(base);
  if (!owner) {
    fail("source.type", "unknown associated component", span);
    return {};
  }
  if (!charge(owner->members.size(), span))
    return {};
  for (auto id : owner->members) {
    auto &decl = declarations[id.index];
    if (decl.name != member)
      continue;
    if (decl.kind != Declaration::Kind::Associated ||
        (complete && !complete(id))) {
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
bool Semantics::checkArguments(const Declaration &target, ArrayRef<Type> args,
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
          actual = &declarations[param->interface->index];
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
    if (!entails(context, goal)) {
      if (diagnostic)
        diagnostic->related.push_back(bound.span);
      return false;
    }
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
                  span, {bound.span});
  }
  return true;
}
bool Semantics::assumptions(const Declaration &caller,
                            const NaturalBound &bound,
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
  return (inferNatural &&
          inferNatural(caller, {l->dimension, r->dimension, span})) ||
         fail("source.bound", "contract does not establish natural bound", span,
              {bound.span});
}

} // namespace zkc::language::detail
