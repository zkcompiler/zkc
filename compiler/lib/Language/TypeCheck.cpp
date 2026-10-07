#include "Checker.h"
#include "zkc/Contracts/Domains.h"
#include "llvm/ADT/StringExtras.h"
#include <algorithm>
#include <limits>
using namespace llvm;
namespace zkc::language::detail {
namespace {
Type parameterType(const Parameter &p) {
  using K = Type::Kind;
  Type value(p.sort == Parameter::Sort::Field       ? K::Field
             : p.sort == Parameter::Sort::Group     ? K::Group
             : p.sort == Parameter::Sort::Natural   ? K::Natural
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
bool runtimeType(const Type &type) {
  return type.kind != Type::Kind::Natural && type.kind != Type::Kind::Component;
}
Permissions intersect(Permissions a, const Permissions &b) {
  return {a.copy && b.copy, a.drop && b.drop, a.share && b.share,
          a.wire && b.wire};
}
} // namespace
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
  std::map<std::string, Natural> nats;
  for (auto &[name, arg] : bindings)
    if (arg.kind == Type::Kind::Natural)
      nats.emplace(name, arg.dimension);
  if (!result.dimension.isClosed()) {
    auto before = naturals.remainingWork();
    auto n = naturals.substitute(result.dimension, nats);
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
  if ((result.kind == Type::Kind::Associated ||
       result.kind == Type::Kind::Field || result.kind == Type::Kind::Group) &&
      !result.arguments.empty()) {
    StringRef name = result.domain;
    auto pos = name.rfind("::");
    return associated(result.arguments.front(), name.drop_front(pos + 2), span);
  }
  return result;
}
std::optional<Type> Checker::associated(const Type &base, StringRef member,
                                        Span span) {
  auto path = member.split("::");
  if (!path.second.empty()) {
    auto next = associated(base, path.first, span);
    if (!next)
      return {};
    return associated(*next, path.second, span);
  }
  if (base.kind == Type::Kind::Group && member == "Scalar") {
    Type result(Type::Kind::Field);
    if (base.symbolic) {
      result.domain = base.domain + "::Scalar";
      result.symbolic = true;
      result.assumptions = {true, true, false, false};
      result.arguments = {base};
    } else {
      result.domain = protocol::installedDomains()
                          .associatedIdentity(base.domain, "Scalar")
                          .str();
      if (result.domain.empty()) {
        fail("source.type", "group has no installed Scalar association", span);
        return {};
      }
    }
    return result;
  }
  if (base.kind != Type::Kind::Component) {
    fail("source.type", "associated member requires a component or group",
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
    if (decl.associatedSort == "Field" || decl.associatedSort == "Group") {
      if (!decl.abstract)
        return substitute(decl.domain, substitution(*owner, base.arguments),
                          span);
      result.kind = decl.associatedSort == "Field" ? Type::Kind::Field
                                                   : Type::Kind::Group;
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
    case Parameter::Sort::Field:
      kind = a.kind == Type::Kind::Field;
      break;
    case Parameter::Sort::Group:
      kind = a.kind == Type::Kind::Group;
      break;
    case Parameter::Sort::Natural:
      kind = a.kind == Type::Kind::Natural;
      break;
    case Parameter::Sort::Type:
      kind = runtimeType(a);
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
    if (runtimeType(a)) {
      auto caps = permissions(a, span, context);
      if (!caps)
        return false;
      if (!caps->includes(p.permissions))
        return fail("source.permission",
                    "static argument lacks required permission", span);
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
    if (!runtimeType(*element) || count->kind != K::Natural) {
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
      if (!runtimeType(*t)) {
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
    auto parts = StringRef(s.name).rsplit("::");
    if (parts.second == "Scalar") {
      auto previous = diagnostic;
      auto base = resolve(context, parts.first, s.span);
      if (base &&
          output.declarations[base->index].kind == Declaration::Kind::Domain &&
          output.declarations[base->index].domain.kind == K::Group)
        return associated(output.declarations[base->index].domain, "Scalar",
                          s.span);
      diagnostic = std::move(previous);
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
bool Checker::requirements(Declaration &decl) {
  for (auto &req : sources[decl.id.index]->requirements) {
    auto lhs = type(decl, req.lhs);
    if (!lhs)
      return false;
    if (!req.permission.empty()) {
      if (lhs->kind == Type::Kind::Natural ||
          lhs->kind == Type::Kind::Component)
        return fail("source.permission", "permissions constrain runtime types",
                    req.span);
      bool matched = false;
      for (auto &p : decl.parameters)
        if (p.atom == lhs->domain) {
          if (req.permission == "Copy")
            p.permissions.copy = true;
          else if (req.permission == "Drop")
            p.permissions.drop = true;
          else if (req.permission == "Share")
            p.permissions.share = true;
          else
            p.permissions.wire = true;
          matched = true;
          break;
        }
      if (!matched) {
        if (!symbolic(*lhs)) {
          auto caps = permissions(*lhs, req.span, &decl);
          if (!caps)
            return false;
          bool holds = req.permission == "Copy"    ? caps->copy
                       : req.permission == "Drop"  ? caps->drop
                       : req.permission == "Share" ? caps->share
                                                   : caps->wire;
          if (!holds)
            return fail("source.permission",
                        "closed permission requirement does not hold",
                        req.span);
          continue;
        }
        if (lhs->arguments.empty() ||
            (lhs->kind != Type::Kind::Associated &&
             lhs->kind != Type::Kind::Field &&
             lhs->kind != Type::Kind::Group) ||
            !symbolic(*lhs))
          return fail("source.permission",
                      "permission requirement must name a parameter or "
                      "associated projection",
                      req.span);
        Permissions caps;
        if (req.permission == "Copy")
          caps.copy = true;
        else if (req.permission == "Drop")
          caps.drop = true;
        else if (req.permission == "Share")
          caps.share = true;
        else
          caps.wire = true;
        decl.permissionBounds.push_back({*lhs, caps, req.span});
      }
    } else {
      auto rhs = type(decl, req.rhs);
      if (!rhs)
        return false;
      if (lhs->kind != Type::Kind::Natural || rhs->kind != Type::Kind::Natural)
        return fail("source.bound", "bound operands must be naturals",
                    req.span);
      if (lhs->dimension.isClosed() && rhs->dimension.isClosed() &&
          lhs->dimension.closedValue() > rhs->dimension.closedValue())
        return fail("source.bound", "closed bound is false", req.span);
      decl.bounds.push_back({lhs->dimension, rhs->dimension, req.span});
    }
  }
  return true;
}
bool Checker::chargeStaticSignature(const Declaration &decl) {
  for (const auto &parameter : decl.parameters) {
    if (!charge(parameter.name.size() + parameter.atom.size() + 1, decl.span))
      return false;
    for (const auto &argument : parameter.arguments)
      if (!chargeType(argument, decl.span))
        return false;
  }
  for (const auto &bound : decl.permissionBounds)
    if (!chargeType(bound.type, decl.span))
      return false;
  for (const auto &bound : decl.bounds)
    for (const Natural *natural : {&bound.lhs, &bound.rhs})
      for (const auto &[factors, coefficient] : natural->terms()) {
        (void)coefficient;
        if (!charge(1, decl.span))
          return false;
        for (const auto &factor : factors)
          if (!charge(factor.size() + 1, decl.span))
            return false;
      }
  return true;
}
bool Checker::signature(DeclarationId id, unsigned depth) {
  auto &decl = output.declarations[id.index];
  auto &source = *sources[id.index];
  if (depth > work.limits.typeDepth)
    return fail("source.limit", "type declaration depth limit", decl.span);
  if (signatureState[id.index] == 2)
    return true;
  if (signatureState[id.index] == 1)
    return fail("source.cycle", "recursive type or static signature",
                decl.span);
  signatureState[id.index] = 1;
  if (decl.parent) {
    if (!signature(*decl.parent, depth + 1))
      return false;
    if (!chargeStaticSignature(output.declarations[decl.parent->index]))
      return false;
    decl.parameters = output.declarations[decl.parent->index].parameters;
    decl.bounds = output.declarations[decl.parent->index].bounds;
    decl.permissionBounds =
        output.declarations[decl.parent->index].permissionBounds;
  }
  std::set<std::string> names;
  for (auto &p : decl.parameters) {
    if (p.name == decl.name)
      return fail("source.shadow",
                  "member shadows an inherited static parameter", decl.span);
    names.insert(p.name);
  }
  formingParameters.insert(id.index);
  for (auto &src : source.parameters) {
    if (!names.insert(src.name).second ||
        visible[decl.module.index].count(src.name))
      return fail("source.shadow", "static parameter shadows a visible name",
                  src.span);
    Parameter p;
    p.name = src.name;
    p.atom = "parameter:" + decl.qualifiedName + "::" + src.name;
    p.span = src.span;
    p.permissions = src.permissions;
    auto name = src.constraint.name;
    if (name == "Type")
      p.sort = Parameter::Sort::Type;
    else if (name == "Field") {
      p.sort = Parameter::Sort::Field;
      p.permissions.copy = p.permissions.drop = true;
    } else if (name == "Group") {
      p.sort = Parameter::Sort::Group;
      p.permissions.copy = p.permissions.drop = true;
    } else if (name == "nat")
      p.sort = Parameter::Sort::Natural;
    else {
      auto target = resolve(decl, name, src.span);
      if (!target || !signature(*target, depth + 1))
        return false;
      auto &interface = output.declarations[target->index];
      if (interface.kind != Declaration::Kind::Interface)
        return fail("source.generic",
                    "component parameter requires an interface", src.span);
      auto args =
          arguments(decl, interface, src.constraint.arguments, src.span);
      if (!args)
        return false;
      p.sort = Parameter::Sort::Component;
      p.interface = *target;
      p.arguments = std::move(*args);
    }
    if (p.sort != Parameter::Sort::Component &&
        !src.constraint.arguments.empty())
      return fail("source.generic", "static sort does not take arguments",
                  src.span);
    if ((p.sort == Parameter::Sort::Natural ||
         p.sort == Parameter::Sort::Component) &&
        !(p.permissions == Permissions{}))
      return fail("source.permission", "permissions constrain runtime types",
                  p.span);
    parameters.emplace(p.atom,
                       std::make_pair(id, unsigned(decl.parameters.size())));
    decl.parameters.push_back(std::move(p));
  }
  formingParameters.erase(id.index);
  if (!requirements(decl))
    return false;
  for (const auto &application : deferredApplications[id.index]) {
    const auto &target = output.declarations[application.target.index];
    if (!checkArguments(target, application.arguments, application.span, &decl))
      return false;
    auto bindings = substitution(target, application.arguments);
    for (const auto &bound : target.bounds)
      if (!assumptions(decl, bound, bindings, application.span))
        return false;
  }
  deferredApplications.erase(id.index);
  if (source.definition) {
    auto def = type(decl, *source.definition, depth + 1);
    if (!def)
      return false;
    if (decl.kind == Declaration::Kind::Component) {
      auto *target = typeDeclaration(*def);
      if (!target || target->kind != Declaration::Kind::Interface)
        return fail("source.conformance",
                    "component must implement an interface", decl.span);
      decl.implementation = *def;
    } else {
      if (!runtimeType(*def))
        return fail("source.type",
                    "alias or representation must denote a runtime type",
                    decl.span);
      if (decl.kind == Declaration::Kind::Associated &&
          ((decl.associatedSort == "Field" && def->kind != Type::Kind::Field) ||
           (decl.associatedSort == "Group" && def->kind != Type::Kind::Group)))
        return fail("source.type",
                    "associated representation has a different domain sort",
                    decl.span);
      decl.domain = *def;
    }
  }
  auto fieldList = [&](ArrayRef<SyntaxPort> from, std::vector<TypeField> &to) {
    std::set<std::string> fields;
    for (auto &src : from) {
      if (!fields.insert(src.name).second)
        return fail("source.duplicate", "duplicate field", src.span);
      auto t = type(decl, src.type, depth + 1);
      if (!t)
        return false;
      if (!runtimeType(*t))
        return fail("source.type", "field cannot contain a static term",
                    src.span);
      to.push_back({src.name, *t, src.isPublic, src.span});
    }
    return true;
  };
  if (!fieldList(source.fields, decl.fields))
    return false;
  std::set<std::string> labels;
  for (auto &src : source.alternatives) {
    if (!labels.insert(src.name).second)
      return fail("source.duplicate", "duplicate variant alternative",
                  src.span);
    Alternative alt;
    alt.name = src.name;
    alt.span = src.span;
    if (!fieldList(src.fields, alt.fields))
      return false;
    decl.alternatives.push_back(std::move(alt));
  }
  if (decl.kind == Declaration::Kind::Variant &&
      (decl.alternatives.empty() || decl.alternatives.size() > 32))
    return fail("source.type", "variant requires one to 32 alternatives",
                decl.span);
  if (decl.kind == Declaration::Kind::Math ||
      decl.kind == Declaration::Kind::Local ||
      decl.kind == Declaration::Kind::Protocol) {
    decl.roles = source.roles;
    std::set<std::string> roster(decl.roles.begin(), decl.roles.end());
    if (roster.size() != decl.roles.size())
      return fail("source.roles", "duplicate participant", decl.span);
    if (decl.roles.size() > 1024)
      return fail("source.limit", "participant roster exceeds target limit",
                  decl.span);
    for (bool input : {true, false}) {
      std::set<std::string> names;
      for (auto &src : input ? source.inputs : source.outputs) {
        if (!names.insert(src.name).second)
          return fail("source.duplicate", "duplicate port", src.span);
        if (input && visible[decl.module.index].count(src.name))
          return fail("source.shadow", "input shadows a visible declaration",
                      src.span);
        auto t = type(decl, src.type, depth + 1);
        if (!t)
          return false;
        if (!runtimeType(*t))
          return fail("source.type", "port cannot contain a static term",
                      src.span);
        Port p{src.name, *t, {}, src.span};
        if (decl.kind == Declaration::Kind::Protocol) {
          auto set = roles(decl, src.roles, src.span);
          if (!set)
            return false;
          p.roles = std::move(*set);
        }
        (input ? decl.inputs : decl.outputs).push_back(std::move(p));
      }
    }
    if (decl.kind == Declaration::Kind::Math && decl.effectAllowance &&
        (decl.effectAllowance->first || decl.effectAllowance->second))
      return fail("source.effect", "math callable cannot allow ordered effects",
                  decl.span);
  }
  signatureState[id.index] = 2;
  return true;
}
std::optional<std::vector<TypeField>>
Checker::fields(const Type &type, Span span, unsigned depth) {
  if (depth > work.limits.typeDepth || !charge(1, span)) {
    if (!diagnostic)
      fail("source.limit", "field expansion depth", span);
    return {};
  }
  std::vector<TypeField> result;
  if (type.kind == Type::Kind::Unit)
    return result;
  if (type.kind == Type::Kind::Tuple) {
    for (unsigned i = 0; i < type.arguments.size(); ++i) {
      if (!chargeType(type.arguments[i], span))
        return {};
      result.push_back({std::to_string(i), type.arguments[i], true, span});
    }
    return result;
  }
  if (type.kind == Type::Kind::Array) {
    if (!type.dimension.isClosed()) {
      fail("source.bound", "array expansion requires a closed length", span);
      return {};
    }
    if (type.dimension.closedValue() > work.limits.aggregateLeaves) {
      fail("source.limit", "array layout exceeds bound", span);
      return {};
    }
    if (!charge(type.dimension.closedValue(), span))
      return {};
    for (uint64_t i = 0; i < type.dimension.closedValue(); ++i) {
      if (!chargeType(type.arguments.front(), span))
        return {};
      result.push_back({std::to_string(i), type.arguments.front(), true, span});
    }
    return result;
  }
  auto *decl = typeDeclaration(type);
  if (!decl || (type.kind != Type::Kind::Record &&
                type.kind != Type::Kind::Associated)) {
    fail("source.type", "type has no product fields; variants require match",
         span);
    return {};
  }
  auto bindings = substitution(*decl, type.arguments);
  if (type.kind == Type::Kind::Associated) {
    if (decl->abstract) {
      fail("source.private", "abstract type representation is unavailable",
           span);
      return {};
    }
    const auto &base = type.arguments.front();
    auto &owner = output.declarations[decl->parent->index];
    bindings = substitution(owner, base.arguments);
    auto repr = substitute(decl->domain, bindings, span, depth + 1);
    if (!repr)
      return {};
    result.push_back({"value", *repr, false, span});
    return result;
  }
  for (const auto &source : decl->fields) {
    auto t = substitute(source.type, bindings, span, depth + 1);
    if (!t)
      return {};
    result.push_back(
        {source.name, std::move(*t), source.isPublic, source.span});
  }
  return result;
}
std::optional<std::vector<Alternative>>
Checker::alternatives(const Type &type, Span span, unsigned depth) {
  auto *decl = typeDeclaration(type);
  if (!decl || decl->kind != Declaration::Kind::Variant) {
    fail("source.type", "match requires a nominal variant", span);
    return {};
  }
  if (depth > work.limits.typeDepth ||
      !charge(decl->alternatives.size(), span)) {
    if (!diagnostic)
      fail("source.limit", "variant expansion depth", span);
    return {};
  }
  for (const auto &alt : decl->alternatives)
    for (const auto &field : alt.fields)
      if (!chargeType(field.type, span))
        return {};
  auto result = decl->alternatives;
  auto bindings = substitution(*decl, type.arguments);
  for (auto &alt : result)
    for (auto &field : alt.fields) {
      auto t = substitute(field.type, bindings, span, depth + 1);
      if (!t)
        return {};
      field.type = std::move(*t);
    }
  return result;
}
std::optional<Permissions> Checker::permissions(const Type &type, Span span,
                                                const Declaration *scope,
                                                unsigned depth) {
  if (depth > work.limits.typeDepth || !charge(1, span)) {
    if (!diagnostic)
      fail("source.limit", "permission expansion depth", span);
    return {};
  }
  using K = Type::Kind;
  auto scoped = [&](Permissions inherent) -> std::optional<Permissions> {
    auto include = [&](Permissions p) {
      inherent = {inherent.copy || p.copy, inherent.drop || p.drop,
                  inherent.share || p.share, inherent.wire || p.wire};
    };
    if (scope) {
      for (const auto &parameter : scope->parameters) {
        if (!charge(parameter.atom.size() + 1, span))
          return {};
        if (parameter.atom == type.domain)
          include(parameter.permissions);
      }
      for (const auto &bound : scope->permissionBounds) {
        if (!chargeType(bound.type, span))
          return {};
        if (type == bound.type)
          include(bound.permissions);
      }
    }
    return inherent;
  };
  if (type.symbolic || type.kind == K::Parameter)
    return scoped(type.assumptions);
  if (type.kind == K::Associated) {
    auto *decl = typeDeclaration(type);
    if (!decl) {
      fail("source.type", "unknown associated type", span);
      return {};
    }
    return scoped(decl->permissions.value_or(Permissions{}));
  }
  if (type.kind == K::Boolean || type.kind == K::Index ||
      type.kind == K::Field || type.kind == K::Group || type.kind == K::Unit)
    return Permissions{true, true, true, true};
  Permissions result{true, true, true, true};
  std::vector<Type> children;
  if (type.kind == K::Tuple || type.kind == K::Array)
    children = type.arguments;
  else if (type.kind == K::Record) {
    auto fs = fields(type, span, depth + 1);
    if (!fs)
      return {};
    for (auto &f : *fs)
      children.push_back(f.type);
  } else if (type.kind == K::Variant) {
    auto alts = alternatives(type, span, depth + 1);
    if (!alts)
      return {};
    for (auto &a : *alts)
      for (auto &f : a.fields)
        children.push_back(f.type);
  } else {
    fail("source.type", "static term has no runtime permissions", span);
    return {};
  }
  for (auto &child : children) {
    auto p = permissions(child, span, scope, depth + 1);
    if (!p)
      return {};
    result = intersect(result, *p);
  }
  if (auto *decl = typeDeclaration(type); decl && decl->permissions) {
    if (!result.includes(*decl->permissions)) {
      fail("source.permission", "declared permissions exceed field permissions",
           decl->span);
      return {};
    }
    result = *decl->permissions;
  }
  return result;
}
bool Checker::constructorAllowed(const Declaration &context,
                                 const Type &type) const {
  auto *decl = typeDeclaration(type);
  return decl &&
         (type.kind == Type::Kind::Record || type.kind == Type::Kind::Variant ||
          type.kind == Type::Kind::Associated) &&
         decl->module.index == context.module.index;
}
bool Checker::ingress(const Type &type, Span span, unsigned depth) {
  if (depth > work.limits.typeDepth || !charge(1, span))
    return diagnostic ? false
                      : fail("source.limit", "ingress type depth", span);
  using K = Type::Kind;
  if (type.kind == K::Associated)
    return fail("source.ingress",
                "private associated value needs an admitted ingress validator",
                span);
  if (type.kind == K::Tuple || type.kind == K::Array) {
    for (auto &t : type.arguments)
      if (!ingress(t, span, depth + 1))
        return false;
  }
  if (type.kind == K::Record) {
    auto *declaration = typeDeclaration(type);
    if (declaration && declaration->permissions)
      return fail("source.ingress",
                  "restricted record requires an admitted ingress validator",
                  span);
    auto fs = fields(type, span, depth + 1);
    if (!fs)
      return false;
    for (auto &f : *fs)
      if (!f.isPublic || !ingress(f.type, span, depth + 1))
        return diagnostic ? false
                          : fail("source.ingress",
                                 "private record field cannot enter through "
                                 "protocol ports or messages",
                                 span);
  }
  if (type.kind == K::Variant) {
    auto *declaration = typeDeclaration(type);
    if (declaration && declaration->permissions)
      return fail("source.ingress",
                  "restricted variant requires an admitted ingress validator",
                  span);
    auto as = alternatives(type, span, depth + 1);
    if (!as)
      return false;
    for (auto &a : *as)
      for (auto &f : a.fields)
        if (!ingress(f.type, span, depth + 1))
          return false;
  }
  return true;
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
  for (auto &given : caller.bounds)
    if (given.lhs == l->dimension && given.rhs == r->dimension)
      return true;
  return fail("source.bound", "generic call needs an explicit natural bound",
              span);
}
bool Checker::representations() {
  std::set<std::string> active, complete;
  std::function<bool(const Type &, Span, unsigned)> visit =
      [&](const Type &type, Span span, unsigned depth) {
        if (depth > work.limits.typeDepth)
          return fail("source.limit", "representation expansion depth", span);
        if (!chargeType(type, span))
          return false;
        if (type.kind == Type::Kind::Parameter || type.symbolic)
          return true;
        auto key = typeIdentity(type);
        if (complete.count(key))
          return true;
        if (!active.insert(key).second)
          return fail("source.cycle", "recursive runtime representation", span);
        if (type.kind == Type::Kind::Array || type.kind == Type::Kind::Tuple) {
          for (const auto &child : type.arguments)
            if (!visit(child, span, depth + 1))
              return false;
        } else if (type.kind == Type::Kind::Record ||
                   type.kind == Type::Kind::Associated) {
          auto *decl = typeDeclaration(type);
          if (!decl || !decl->abstract) {
            auto children = fields(type, span, depth + 1);
            if (!children)
              return false;
            for (const auto &child : *children)
              if (!visit(child.type, child.span, depth + 1))
                return false;
          }
        } else if (type.kind == Type::Kind::Variant) {
          auto children = alternatives(type, span, depth + 1);
          if (!children)
            return false;
          for (const auto &alternative : *children)
            for (const auto &child : alternative.fields)
              if (!visit(child.type, child.span, depth + 1))
                return false;
        }
        active.erase(key);
        complete.insert(std::move(key));
        return true;
      };
  for (const auto &decl : output.declarations) {
    if (decl.kind == Declaration::Kind::Associated && !decl.abstract &&
        !visit(decl.domain, decl.span, 1))
      return false;
    for (const auto *ports : {&decl.inputs, &decl.outputs})
      for (const auto &port : *ports)
        if (!visit(port.type, port.span, 1))
          return false;
  }
  return true;
}
bool Checker::conformance(DeclarationId id) {
  auto &component = output.declarations[id.index];
  auto &selected = *component.implementation;
  auto *interface = typeDeclaration(selected);
  auto bindings = substitution(*interface, selected.arguments);
  Type self(Type::Kind::Component, component.qualifiedName);
  for (auto &p : component.parameters)
    self.arguments.push_back(parameterType(p));
  bindings.emplace("self:" + interface->qualifiedName, self);
  if (interface->members.size() != component.members.size())
    return fail("source.conformance",
                "component must implement every member exactly once",
                component.span);
  for (auto requiredId : interface->members) {
    auto &required = output.declarations[requiredId.index];
    const Declaration *provided = nullptr;
    for (auto providedId : component.members)
      if (output.declarations[providedId.index].name == required.name)
        provided = &output.declarations[providedId.index];
    if (!provided || provided->kind != required.kind)
      return fail("source.conformance",
                  "component member missing or has a different callable mode",
                  component.span);
    if (required.kind == Declaration::Kind::Associated) {
      auto sort = required.associatedSort;
      if ((sort == "Field" && provided->domain.kind != Type::Kind::Field) ||
          (sort == "Group" && provided->domain.kind != Type::Kind::Group) ||
          ((sort == "Field" || sort == "Group") &&
           provided->associatedSort != sort))
        return fail("source.conformance", "associated domain sort differs",
                    provided->span);
      if (!provided->permissions.value_or(Permissions{})
               .includes(required.permissions.value_or(Permissions{})))
        return fail("source.conformance",
                    "associated type lacks promised permissions",
                    provided->span);
      auto caps = permissions(provided->domain, provided->span, &component);
      if (!caps)
        return false;
      if (!caps->includes(provided->permissions.value_or(Permissions{})))
        return fail("source.permission",
                    "associated permissions exceed representation",
                    provided->span);
    } else {
      if (required.inputs.size() != provided->inputs.size() ||
          required.outputs.size() != provided->outputs.size())
        return fail("source.conformance", "member arity differs",
                    provided->span);
      if (required.parameters.size() != interface->parameters.size() ||
          provided->parameters.size() != component.parameters.size())
        return fail("source.unsupported",
                    "member-level generic parameters need a separate "
                    "conformance contract",
                    provided->span);
      if (!chargeStaticSignature(component))
        return false;
      Declaration available{};
      available.span = component.span;
      available.parameters = component.parameters;
      available.bounds = component.bounds;
      available.permissionBounds = component.permissionBounds;
      for (const auto &parameter : required.parameters) {
        auto actual = bindings.find(parameter.atom);
        if (actual != bindings.end() &&
            !(parameter.permissions == Permissions{})) {
          if (!chargeType(actual->second, provided->span))
            return false;
          available.permissionBounds.push_back(
              {actual->second, parameter.permissions, parameter.span});
        }
      }
      for (const auto &bound : required.bounds) {
        Type lhs(Type::Kind::Natural), rhs(Type::Kind::Natural);
        lhs.dimension = bound.lhs;
        rhs.dimension = bound.rhs;
        auto l = substitute(lhs, bindings, provided->span);
        auto r = substitute(rhs, bindings, provided->span);
        if (!l || !r)
          return false;
        available.bounds.push_back({l->dimension, r->dimension, bound.span});
      }
      for (const auto &bound : required.permissionBounds) {
        auto type = substitute(bound.type, bindings, provided->span);
        if (!type)
          return false;
        available.permissionBounds.push_back(
            {*type, bound.permissions, bound.span});
      }
      for (const auto &bound : provided->permissionBounds) {
        Type requirement = bound.type;
        requirement.assumptions = {};
        auto resolved = substitute(requirement, {}, provided->span);
        if (!resolved)
          return false;
        auto caps = permissions(*resolved, provided->span, &available);
        if (!caps)
          return false;
        if (!caps->includes(bound.permissions))
          return fail("source.conformance",
                      "member adds an associated permission precondition",
                      provided->span);
      }
      for (const auto &bound : provided->bounds)
        if (!assumptions(available, bound, {}, provided->span))
          return false;
      for (unsigned i = 0; i < provided->parameters.size(); ++i) {
        if (provided->parameters[i].sort == Parameter::Sort::Natural ||
            provided->parameters[i].sort == Parameter::Sort::Component)
          continue;
        auto allowed = permissions(parameterType(component.parameters[i]),
                                   provided->span, &available);
        if (!allowed)
          return false;
        if (!allowed->includes(provided->parameters[i].permissions))
          return fail("source.conformance",
                      "member adds a permission precondition", provided->span);
      }
      for (bool input : {true, false}) {
        auto &a = input ? required.inputs : required.outputs;
        auto &b = input ? provided->inputs : provided->outputs;
        for (unsigned i = 0; i < a.size(); ++i) {
          auto expected = substitute(a[i].type, bindings, provided->span);
          if (!expected)
            return false;
          if (*expected != b[i].type)
            return fail("source.conformance", "member signature differs",
                        provided->span);
        }
      }
      auto allowance = required.effectAllowance.value_or(
          std::make_pair(required.kind == Declaration::Kind::Local,
                         required.kind == Declaration::Kind::Local));
      auto &mutableProvided = output.declarations[provided->id.index];
      if (mutableProvided.effectAllowance) {
        auto p = *mutableProvided.effectAllowance;
        if ((p.first && !allowance.first) || (p.second && !allowance.second))
          return fail("source.conformance",
                      "member effect allowance exceeds interface",
                      provided->span);
      } else
        mutableProvided.effectAllowance = allowance;
    }
  }
  return true;
}
} // namespace zkc::language::detail
