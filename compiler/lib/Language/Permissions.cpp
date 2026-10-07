#include "Checker.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
namespace {
Permissions intersect(Permissions a, const Permissions &b) {
  return {a.copy && b.copy, a.drop && b.drop, a.share && b.share,
          a.wire && b.wire};
}
} // namespace
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
    for (auto &f : *fs) {
      children.push_back(f.type);
      result.wire &= f.isPublic;
    }
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
    // Explicit nominal permissions seal constructor authority. Without a
    // declared validator, that authority cannot arrive from a wire decoder.
    result.wire = false;
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
bool Checker::ingress(const Type &type, Span span) {
  auto caps = permissions(type, span);
  return caps &&
         (caps->wire ||
          fail("source.ingress",
               "Entry input requires Wire or an admitted ingress validator",
               span));
}

} // namespace zkc::language::detail
