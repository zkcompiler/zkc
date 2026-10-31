#include "Semantics.h"
#include "zkc/Language/Builtins.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/ScopeExit.h"
using namespace llvm;
namespace zkc::language::detail {
Semantics::Semantics(const std::vector<Declaration> &declarations,
                     ArrayRef<Asset> assets, Work &work,
                     std::function<bool(DeclarationId)> complete)
    : work(work), naturals(work.limits.work, work.limits.naturalTerms,
                           work.limits.naturalFactors),
      declarations(declarations), assets(assets),
      complete(std::move(complete)) {
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
  Type value =
      p.sort == Parameter::Sort::Domain ? domainType(p.domainSort, p.atom)
      : p.sort == Parameter::Sort::Asset
          ? assetType(p.domainSort, p.atom)
          : Type(p.sort == Parameter::Sort::Natural      ? K::Natural
                 : p.sort == Parameter::Sort::Module     ? K::Module
                 : p.sort == Parameter::Sort::OracleKind ? K::OracleKind
                                                         : K::Parameter,
                 p.atom);
  value.symbolic = true;
  value.assumptions = p.permissions;
  if (p.sort == Parameter::Sort::Natural)
    value.dimension = cantFail(Natural::atom(p.atom));
  if (p.sort == Parameter::Sort::Module)
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
bool Semantics::protocolValue(const Type &type, Span span) {
  if (type.kind == Type::Kind::LogicalRecord)
    return logicalRecord(type, span);
  return isOracleHandle(type) || executableType(type, span);
}
bool Semantics::oraclePort(const Port &port) {
  if (isLogicalValue(port.type) != port.oracle.has_value())
    return fail("source.oracle-port",
                "oracle ports require an explicit holder and receiver arrow",
                port.span);
  if (!port.oracle)
    return true;
  if (port.roles.size() < 2 ||
      !llvm::is_contained(port.roles, port.oracle->holder))
    return fail("source.oracle-port", "invalid oracle port role family",
                port.span);
  if (port.type.kind == Type::Kind::LogicalRecord) {
    if (port.oracle->maximumRows)
      return fail("source.oracle-shape",
                  "logical record row bounds belong to direct fields",
                  port.span);
    return logicalRecord(port.type, port.span);
  }
  unsigned arity = port.type.kind == Type::Kind::OracleSequence ? 2 : 1;
  if (port.type.arguments.size() != arity)
    return fail("source.oracle-port", "invalid oracle port type", port.span);
  if (port.oracle->maximumRows &&
      port.oracle->maximumRows->kind != Type::Kind::Natural)
    return fail("source.oracle-shape",
                "oracle maximum must be a static natural", port.span);
  const auto &kind = port.type.arguments.front();
  if (!kind.arguments.empty() &&
      ((kind.arguments.size() == 2) == port.oracle->maximumRows.has_value()))
    return fail("source.oracle-shape",
                "only an unsized oracle port requires an explicit maximum",
                port.span);
  return true;
}
bool Semantics::chargeConstruction(const ConstructionDefinition &value,
                                   Span span) {
  if (!charge(value.suite.size() + value.rules.size() +
                  value.applications.size() + 1,
              span))
    return false;
  for (const auto *type : {&value.provider, &value.state})
    if (*type && !chargeType(**type, span))
      return false;
  if (value.initializer && value.initializer->module &&
      !chargeType(*value.initializer->module, span))
    return false;
  for (const auto *arguments : {&value.arguments, &value.initializerArguments})
    for (const auto &argument : *arguments)
      if (!chargeType(argument, span))
        return false;
  if (value.codec) {
    const auto &codec = *value.codec;
    if (!chargeType(codec.provider, span) || !chargeType(codec.record, span) ||
        !charge(codec.inputs.size() + 1, span))
      return false;
    for (const auto *method :
         {&codec.initialize, &codec.write, &codec.finish}) {
      if (method->target.module && !chargeType(*method->target.module, span))
        return false;
      for (const auto &argument : method->arguments)
        if (!chargeType(argument, span))
          return false;
    }
  }
  for (const auto &application : value.applications) {
    for (const auto &part : application.path)
      if (!charge(part.size() + 1, application.span))
        return false;
    for (const auto &argument : application.arguments)
      if (!chargeType(argument, application.span))
        return false;
  }
  for (const auto &rule : value.rules) {
    if (!charge(rule.inputs.size() + 1, rule.span))
      return false;
    for (const auto &part : rule.path)
      if (!charge(part.size() + 1, rule.span))
        return false;
    for (const auto &argument : rule.arguments)
      if (!chargeType(argument, rule.span))
        return false;
    for (const auto *type : {&rule.payload, &rule.chunks})
      if (*type && !chargeType(**type, rule.span))
        return false;
  }
  return true;
}
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
  if (type.kind != K::Record && type.kind != K::LogicalRecord &&
      type.kind != K::Variant && type.kind != K::Associated &&
      type.kind != K::Module)
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
    // A projection of a bound asset atom is decided here, from the captured
    // asset or by renaming, before the polynomial is normalized.
    std::map<std::pair<std::string, std::string>, Natural> projections;
    for (const auto &[factors, coefficient] : result.dimension.terms()) {
      (void)coefficient;
      if (!charge(factors.size() + 1, span))
        return {};
      for (const auto &factor : factors) {
        if (factor.kind != Natural::Factor::Kind::Projection)
          continue;
        auto found = bindings.find(factor.name);
        if (found == bindings.end())
          continue;
        auto key = std::make_pair(factor.name, factor.member);
        if (projections.count(key))
          continue;
        auto value = assetProjection(found->second, factor.member, span);
        if (!value)
          return {};
        projections.emplace(std::move(key), std::move(value->dimension));
      }
    }
    auto before = naturals.remainingWork();
    auto n = naturals.substitute(
        result.dimension,
        [&](const Natural::Factor &factor) -> const Natural * {
          if (factor.kind == Natural::Factor::Kind::Projection) {
            auto found =
                projections.find(std::make_pair(factor.name, factor.member));
            return found == projections.end() ? nullptr : &found->second;
          }
          auto found = bindings.find(factor.name);
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
  if (result.kind == Type::Kind::OracleKind && !symbolic(result) &&
      !oracleKind(result, span))
    return {};
  if (result.kind == Type::Kind::OracleProjection &&
      result.arguments.size() == 1)
    return associated(result.arguments.front(), result.domain, span);
  if ((result.kind == Type::Kind::Associated || !domainSort(result).empty()) &&
      !result.arguments.empty()) {
    StringRef name = result.domain;
    auto pos = name.rfind("::");
    return associated(result.arguments.front(), name.drop_front(pos + 2), span);
  }
  // Substitution must not introduce a logical value into an ordinary product,
  // even when an array has no elements in its eventual native layout.
  if (result.kind == Type::Kind::Array || result.kind == Type::Kind::Tuple ||
      result.kind == Type::Kind::Builtin)
    for (const auto &argument : result.arguments)
      if (isLogicalValue(argument)) {
        fail("source.oracle-aggregate",
             "ordinary aggregates cannot contain logical protocol values",
             span);
        return {};
      }
  if (result.kind == Type::Kind::LogicalRecord && !logicalRecord(result, span))
    return {};
  return result;
}
bool Semantics::oracleKind(const Type &kind, Span span,
                           const Declaration *scope) {
  auto formed = builtinType(oracleConstructor(kind), kind.arguments);
  if (!formed) {
    accept(formed.takeError(), span);
    return false;
  }
  const auto &row = kind.arguments.front();
  return executableType(row, span) && mathematicalData(row, span, scope) &&
         admit(row, Boundary::Participants, span, scope);
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
  if (base.kind == Type::Kind::OracleKind) {
    auto result = oracleMember(base, member);
    if (!result) {
      accept(result.takeError(), span);
      return {};
    }
    return std::move(*result);
  }
  if (base.kind == Type::Kind::Asset)
    return assetProjection(base, member, span);
  if (!domainSort(base).empty()) {
    auto result = domainMember(base, member);
    if (!result) {
      fail("source.type", toString(result.takeError()), span);
      return {};
    }
    return std::move(*result);
  }
  if (base.kind != Type::Kind::Module) {
    fail("source.type", "associated member requires a module or domain", span);
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
    fail("source.type", "unknown associated module", span);
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
std::optional<Substitution>
Semantics::boundMemberSubstitution(const Declaration &callee,
                                   const Type &module, Span span) {
  if (!callee.parent) {
    fail("source.call", "bound callable has no interface owner", span);
    return {};
  }
  const auto &parent = declarations[callee.parent->index];
  Type interface = module;
  if (!module.symbolic && parent.kind == Declaration::Kind::Interface) {
    const auto *owner = typeDeclaration(module);
    if (!owner || !owner->implementation) {
      fail("source.conformance", "bound callable requires a module", span);
      return {};
    }
    auto selected = substitute(*owner->implementation,
                               substitution(*owner, module.arguments), span);
    if (!selected)
      return {};
    interface = std::move(*selected);
  }
  if (interface.arguments.size() != parent.parameters.size() ||
      callee.parameters.size() < parent.parameters.size()) {
    fail("source.conformance", "bound member static arguments differ", span);
    return {};
  }
  Substitution result;
  for (unsigned i = 0; i < parent.parameters.size(); ++i)
    result.emplace(callee.parameters[i].atom, interface.arguments[i]);
  result.emplace("self:" + parent.qualifiedName, module);
  return result;
}

bool Semantics::checkArgumentSorts(const Declaration &target,
                                   ArrayRef<Type> args, Span span,
                                   const Substitution &extra) {
  if (!charge(args.size() + 1, span))
    return false;
  std::vector<std::optional<Type>> known(args.begin(), args.end());
  return checkKnownArgumentSorts(target, known, span, extra);
}
bool Semantics::checkKnownArgumentSorts(const Declaration &target,
                                        ArrayRef<std::optional<Type>> args,
                                        Span span, const Substitution &extra) {
  if (args.size() != target.parameters.size())
    return fail("source.generic", "static argument count differs", span);
  Substitution subst = extra;
  std::set<std::string> unknown;
  for (unsigned i = 0; i < args.size(); ++i)
    if (args[i])
      subst.insert_or_assign(target.parameters[i].atom, *args[i]);
    else
      unknown.insert(target.parameters[i].atom);
  std::function<bool(const Type &)> ready = [&](const Type &type) {
    if (unknown.count(type.domain))
      return false;
    for (const auto &[factors, coefficient] : type.dimension.terms()) {
      (void)coefficient;
      for (const auto &factor : factors)
        if (unknown.count(factor.name))
          return false;
    }
    return llvm::all_of(type.arguments, ready);
  };
  for (unsigned i = 0; i < args.size(); ++i) {
    if (!args[i])
      continue;
    auto &p = target.parameters[i];
    auto &a = *args[i];
    bool kind = false;
    switch (p.sort) {
    case Parameter::Sort::Domain:
      kind = domainSort(a) == p.domainSort;
      break;
    case Parameter::Sort::Asset:
      kind = assetSort(a) == p.domainSort;
      break;
    case Parameter::Sort::Natural:
      kind = a.kind == Type::Kind::Natural;
      break;
    case Parameter::Sort::OracleKind:
      kind = a.kind == Type::Kind::OracleKind;
      break;
    case Parameter::Sort::Type:
      kind = valueType(a);
      if (kind && !executableType(a, span))
        return false;
      break;
    case Parameter::Sort::Module: {
      kind = a.kind == Type::Kind::Module;
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
        auto module = typeDeclaration(a);
        if (module && module->implementation) {
          auto selected = substitute(*module->implementation,
                                     substitution(*module, a.arguments), span);
          if (!selected)
            return false;
          actual = typeDeclaration(*selected);
          actualArgs = selected->arguments;
        }
      }
      if (!actual || !p.interface || actual->id.index != p.interface->index)
        return fail("source.conformance",
                    "module does not implement required interface", span);
      if (actualArgs.size() != p.arguments.size())
        return fail("source.conformance", "interface static arguments differ",
                    span);
      for (unsigned j = 0; j < p.arguments.size(); ++j) {
        if (!chargeType(p.arguments[j], span))
          return false;
        if (!ready(p.arguments[j]))
          continue;
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
  }
  return true;
}
bool Semantics::checkArguments(const Declaration &target, ArrayRef<Type> args,
                               Span span, const Declaration *context,
                               const Substitution &extra) {
  if (!checkArgumentSorts(target, args, span, extra))
    return false;
  auto subst = substitution(target, args);
  subst.insert(extra.begin(), extra.end());
  auto satisfies = [&](const Type &type, Permissions required,
                       StringRef message) {
    if (required.copy && !requireUsage(type, Usage::Copy, span, context,
                                       "source.permission", message))
      return false;
    if (required.drop && !required.copy &&
        !requireUsage(type, Usage::Drop, span, context, "source.permission",
                      message))
      return false;
    return true;
  };
  for (unsigned i = 0; i < args.size(); ++i) {
    const auto &p = target.parameters[i];
    const auto &a = args[i];
    if (valueType(a)) {
      if (!satisfies(a, p.permissions,
                     "static argument lacks required permission"))
        return false;
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
    if (!satisfies(*actual, bound.permissions,
                   "type lacks required usage property")) {
      if (diagnostic)
        diagnostic->related.push_back(bound.span);
      return false;
    }
  }
  for (const auto &obligation : target.admissions) {
    auto actual = substitute(obligation.type, subst, span);
    if (!actual || !charge(obligation.calls.size() + 1, span))
      return false;
    auto calls = obligation.calls;
    calls.push_back(span);
    if (!admit(*actual, obligation.boundary, obligation.span, context, calls))
      return false;
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
