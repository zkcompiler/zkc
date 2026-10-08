#include "Checker.h"
#include "zkc/Contracts/NativePolicy.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Language/Builtins.h"
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
  if (isStaticOnly(type)) {
    fail("source.type", "static term has no runtime permissions", span);
    return {};
  }
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
  if (type.kind == K::Formal)
    return Permissions{true, true, false, false};
  if (type.kind == K::Builtin) {
    auto formed = builtinType(type.domain, type.arguments);
    if (!formed) {
      fail("source.builtin", toString(formed.takeError()), span);
      return {};
    }
    const auto *base = protocol::typePermissions(type.domain);
    auto head = protocol::nativeTypeConstructorPolicy(type.domain);
    if (!head) {
      fail("source.builtin", "native data lacks an installed type policy",
           span);
      return {};
    }
    Permissions result{base && base->copy, base && base->drop,
                       head->shared || type.domain == "sequence", true};
    for (const auto &argument : type.arguments) {
      if (isStaticOnly(argument))
        continue;
      auto child = permissions(argument, span, scope, depth + 1);
      if (!child)
        return {};
      result = intersect(result, *child);
    }
    if (!symbolic(type)) {
      auto native = builtinLayout(type);
      if (!native) {
        fail("source.builtin", toString(native.takeError()), span);
        return {};
      }
      auto policy = protocol::nativeTypePolicy(*native);
      result.share &= policy && policy->shared;
      result.wire &= policy && protocol::nativeMessageData(*native);
    } else {
      // Generic message shapes still need a concrete admitted codec at closure.
      result.wire &= type.domain == "vector" || type.domain == "matrix" ||
                     type.domain == "groups" || type.domain == "indices" ||
                     type.domain == "sequence" ||
                     type.domain == "field_array" ||
                     type.domain == "commitment" || type.domain == "proof";
    }
    return result;
  }
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
bool Checker::executableType(const Type &type, Span span, unsigned depth) {
  if (depth > work.limits.typeDepth || !charge(1, span))
    return diagnostic ? false
                      : fail("source.limit", "executable type depth", span);
  using K = Type::Kind;
  if (type.kind == K::Formal)
    return fail("source.formal",
                "formal values cannot cross an executable boundary", span);
  if (type.kind == K::Array || type.kind == K::Tuple ||
      type.kind == K::Builtin) {
    for (const auto &child : type.arguments)
      if (!executableType(child, span, depth + 1))
        return false;
  } else if (type.kind == K::Record || type.kind == K::Associated) {
    auto *decl = typeDeclaration(type);
    if (type.kind == K::Associated && decl && decl->abstract)
      return true;
    auto children = fields(type, span, depth + 1);
    if (!children)
      return false;
    for (const auto &child : *children)
      if (!executableType(child.type, span, depth + 1))
        return false;
  } else if (type.kind == K::Variant) {
    auto alts = alternatives(type, span, depth + 1);
    if (!alts)
      return false;
    for (const auto &alt : *alts)
      for (const auto &child : alt.fields)
        if (!executableType(child.type, span, depth + 1))
          return false;
  }
  return true;
}
bool Checker::mathematicalData(const Type &type, Span span,
                               const Declaration *scope, unsigned depth) {
  if (depth > work.limits.typeDepth || !charge(1, span))
    return diagnostic ? false
                      : fail("source.limit", "mathematical type depth", span);
  auto caps = permissions(type, span, scope, depth);
  if (!caps || !caps->copy || !caps->drop)
    return diagnostic ? false
                      : fail("source.mode",
                             "mathematical values require Copy and Drop", span);
  using K = Type::Kind;
  if (type.kind == K::Builtin) {
    auto policy = protocol::nativeTypeConstructorPolicy(type.domain);
    if (!policy || (!policy->total && type.domain != "sequence"))
      return fail("source.mode",
                  "native data is outside the mathematical vocabulary", span);
    for (const auto &arg : type.arguments)
      if (!isStaticOnly(arg) && !mathematicalData(arg, span, scope, depth + 1))
        return false;
  } else if (type.kind == K::Tuple || type.kind == K::Array) {
    for (const auto &arg : type.arguments)
      if (!mathematicalData(arg, span, scope, depth + 1))
        return false;
  } else if (type.kind == K::Record || type.kind == K::Associated) {
    if (type.kind == K::Associated && symbolic(type))
      return true;
    auto children = fields(type, span, depth + 1);
    if (!children)
      return false;
    for (const auto &child : *children)
      if (!mathematicalData(child.type, span, scope, depth + 1))
        return false;
  } else if (type.kind == K::Variant) {
    auto alts = alternatives(type, span, depth + 1);
    if (!alts)
      return false;
    for (const auto &alt : *alts)
      for (const auto &child : alt.fields)
        if (!mathematicalData(child.type, span, scope, depth + 1))
          return false;
  }
  return true;
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
  if (!executableType(type, span))
    return false;
  auto caps = permissions(type, span);
  return caps &&
         (caps->wire ||
          fail("source.ingress",
               "external input requires Wire or an admitted ingress validator",
               span));
}

std::optional<Type> Checker::projectedType(const Declaration &decl, Type type,
                                           ArrayRef<unsigned> path, Span span) {
  if (!charge(path.size() + 1, span))
    return {};
  for (auto index : path) {
    if (!chargeType(type, span))
      return {};
    if (type.kind == Type::Kind::Array) {
      if (type.dimension.isClosed() && index >= type.dimension.closedValue()) {
        fail("source.index", "static array index is out of range", span);
        return {};
      }
      if (!type.dimension.isClosed()) {
        NaturalBound required{Natural::constant(uint64_t(index) + 1),
                              type.dimension, span};
        if (!assumptions(decl, required, {}, span))
          return {};
      }
      auto element = type.arguments.front();
      type = std::move(element);
    } else {
      auto fs = fields(type, span);
      if (!fs)
        return {};
      if (index >= fs->size()) {
        fail("source.index", "product index is out of range", span);
        return {};
      }
      type = (*fs)[index].type;
    }
  }
  return type;
}
std::optional<unsigned> Checker::fieldIndex(const Declaration &decl,
                                            const Type &type, StringRef name,
                                            Span span) {
  auto *nominal = typeDeclaration(type);
  if (type.kind == Type::Kind::Associated ||
      type.kind == Type::Kind::Parameter || (nominal && nominal->permissions)) {
    fail("source.private",
         "restricted values require their module's unpack or consume operation",
         span);
    return {};
  }
  unsigned index;
  if (type.kind == Type::Kind::Array) {
    if (name.getAsInteger(10, index)) {
      fail("source.index", "fixed arrays require a static numeric index", span);
      return {};
    }
    return index;
  }
  auto product = fields(type, span);
  if (!product)
    return {};
  auto found = llvm::find_if(
      *product, [&](const auto &field) { return field.name == name; });
  if (found == product->end()) {
    fail("source.field", "unknown field: " + name, span);
    return {};
  }
  if (!found->isPublic && !constructorAllowed(decl, type)) {
    fail("source.private", "private record field", span);
    return {};
  }
  return unsigned(found - product->begin());
}
} // namespace zkc::language::detail
