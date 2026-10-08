#include "Checker.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Language/Builtins.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
bool Checker::requirements(Declaration &decl) {
  for (auto &req : sources[decl.id.index]->requirements) {
    if (!req.capability.empty()) {
      if (decl.kind == Declaration::Kind::Associated)
        return fail("source.unsupported",
                    "associated members cannot declare capability bounds",
                    req.span);
      auto name = StringRef(req.capability).rsplit("::");
      auto exports = protocol::sourceCapabilityExports();
      auto found = llvm::find_if(exports, [&](const auto &exported) {
        return exported.module == name.first && exported.name == name.second;
      });
      if (found == exports.end())
        return fail("source.capability",
                    "expected a qualified installed capability export",
                    req.span);
      CapabilityBound bound{found->predicate, {}, req.span};
      for (const auto &syntax : req.arguments) {
        auto argument = type(decl, syntax);
        if (!argument)
          return false;
        bound.arguments.push_back(std::move(*argument));
      }
      if (llvm::none_of(bound.arguments,
                        [&](const auto &t) { return symbolic(t); })) {
        if (!entails(nullptr, bound))
          return false;
      } else {
        if (!capabilityFormation(bound))
          return false;
        // Only open facts are stored. Closed requirements are decided above.
        decl.capabilityBounds.push_back(std::move(bound));
      }
      continue;
    }
    auto lhs = type(decl, req.lhs);
    if (!lhs)
      return false;
    if (!req.permission.empty()) {
      if (isStaticOnly(*lhs))
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
  for (const auto &bound : decl.capabilityBounds) {
    if (!charge(bound.predicate.size() + 1, bound.span))
      return false;
    for (const auto &argument : bound.arguments)
      if (!chargeType(argument, bound.span))
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
          if (!charge(factor.name.size() + 1, decl.span))
            return false;
      }
  return true;
}
bool Checker::signature(DeclarationId id, unsigned depth) {
  auto &decl = output.declarations[id.index];
  if (depth > work.limits.typeDepth)
    return fail("source.limit", "type declaration depth limit", decl.span);
  if (signatureState[id.index] == 2)
    return true;
  if (signatureState[id.index] == 1)
    return fail("source.cycle", "recursive type or static signature",
                decl.span);
  if (decl.kind == Declaration::Kind::Associated) {
    if (!decl.associatedSort.empty() && decl.associatedSort != "Type" &&
        !isDomainSort(decl.associatedSort))
      return fail("source.type", "unknown associated domain sort", decl.span);
    if (decl.associatedSort == "Field" || decl.associatedSort == "Group") {
      if (!decl.permissions)
        decl.permissions.emplace();
      decl.permissions->copy = decl.permissions->drop = true;
    }
  }
  auto &source = *sources[id.index];
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
    decl.capabilityBounds =
        output.declarations[decl.parent->index].capabilityBounds;
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
    else if (isDomainSort(name)) {
      p.sort = Parameter::Sort::Domain;
      p.domainSort = name;
      if (name == "Field" || name == "Group")
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
    if (isStaticOnly(parameterType(p)) && !(p.permissions == Permissions{}))
      return fail("source.permission", "permissions constrain runtime types",
                  p.span);
    parameters.emplace(p.atom,
                       std::make_pair(id, unsigned(decl.parameters.size())));
    decl.parameters.push_back(std::move(p));
  }
  if (!requirements(decl))
    return false;
  formingParameters.erase(id.index);
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
      bool domain = decl.kind == Declaration::Kind::Associated &&
                    isDomainSort(decl.associatedSort);
      if (!domain && !valueType(*def))
        return fail("source.type",
                    "alias or representation must denote a value type",
                    decl.span);
      if (decl.kind == Declaration::Kind::Associated && !domain &&
          !executableType(*def, decl.span))
        return false;
      if (domain && domainSort(*def) != decl.associatedSort)
        return fail("source.type",
                    "associated representation has a different domain sort",
                    decl.span);
      decl.domain = *def;
    }
  }
  if (decl.kind == Declaration::Kind::Associated && !decl.abstract &&
      !isDomainSort(decl.associatedSort) && decl.permissions &&
      decl.permissions->wire)
    return fail("source.permission",
                "private associated Wire requires an admitted validator",
                decl.span);
  if (decl.kind == Declaration::Kind::Associated &&
      isDomainSort(decl.associatedSort) && decl.associatedSort != "Field" &&
      decl.associatedSort != "Group" &&
      !(decl.permissions.value_or(Permissions{}) == Permissions{}))
    return fail("source.permission", "permissions constrain runtime types",
                decl.span);
  auto fieldList = [&](ArrayRef<SyntaxPort> from, std::vector<TypeField> &to) {
    std::set<std::string> fields;
    for (auto &src : from) {
      if (!fields.insert(src.name).second)
        return fail("source.duplicate", "duplicate field", src.span);
      auto t = type(decl, src.type, depth + 1);
      if (!t)
        return false;
      if (!valueType(*t))
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
    for (const auto &field : alt.fields)
      if (!executableType(field.type, field.span))
        return false;
    decl.alternatives.push_back(std::move(alt));
  }
  if (decl.kind == Declaration::Kind::Variant &&
      (decl.alternatives.empty() || decl.alternatives.size() > 32))
    return fail("source.type", "variant requires one to 32 alternatives",
                decl.span);
  if (decl.kind == Declaration::Kind::Math ||
      decl.kind == Declaration::Kind::Local ||
      decl.kind == Declaration::Kind::Protocol ||
      decl.kind == Declaration::Kind::Relation) {
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
        std::optional<Type> t;
        if (input && src.binding) {
          const auto &owner = output.declarations[decl.parent->index];
          auto selected = selector(owner, *src.binding);
          if (!selected)
            return false;
          t = selectedType(owner, *selected);
          inlineBindings[decl.id.index].push_back(std::move(*selected));
        } else
          t = type(decl, src.type, depth + 1);
        if (!t)
          return false;
        if (!valueType(*t))
          return fail("source.type", "port cannot contain a static term",
                      src.span);
        if (decl.kind != Declaration::Kind::Math &&
            !executableType(*t, src.span))
          return false;
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
    for (const auto &src : source.services) {
      if (decl.kind != Declaration::Kind::Protocol ||
          src.type.kind != SyntaxType::Kind::Name ||
          src.type.name != "Random" || src.type.arguments.size() != 1)
        return fail("source.service", "expected a Random<Field> managed port",
                    src.span);
      if (!bindingName(decl, src.name, src.span) ||
          llvm::any_of(decl.inputs,
                       [&](const auto &p) { return p.name == src.name; }) ||
          llvm::any_of(decl.services,
                       [&](const auto &p) { return p.name == src.name; }))
        return diagnostic ? false
                          : fail("source.shadow",
                                 "duplicate service or data binding", src.span);
      auto field = type(decl, src.type.arguments.front(), depth + 1);
      auto owner = roles(decl, src.roles, src.span);
      if (!field || !owner)
        return false;
      if (field->kind != Type::Kind::Field || owner->size() != 1)
        return fail("source.service",
                    "managed random service requires a field and one owner",
                    src.span);
      decl.services.push_back({src.name, *field, owner->front(), src.span, {}});
    }
    if (decl.kind == Declaration::Kind::Math && decl.effectAllowance &&
        (decl.effectAllowance->mayStop || decl.effectAllowance->opaque))
      return fail("source.effect", "math callable cannot allow ordered effects",
                  decl.span);
  }
  if (decl.kind == Declaration::Kind::Relation && !relation(decl))
    return false;
  signatureState[id.index] = 2;
  return true;
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
} // namespace zkc::language::detail
