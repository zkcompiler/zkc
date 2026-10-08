#include "zkc/Language/Layout.h"
#include "Internal.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/NativePolicy.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Language/Builtins.h"
#include "zkc/Support/FramedHash.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include <limits>
using namespace llvm;
namespace zkc::language {
Expected<std::string> LayoutIdentities::get(const Layout &layout) {
  if (auto found = cache.find(&layout); found != cache.end())
    return found->second;
  auto key = typeIdentity(layout.type);
  if (key.size() > remaining)
    return error("source.limit", "schema type identity limit exceeded");
  remaining -= key.size();
  FramedHash hash(remaining);
  hash.frame("zkc.language.schema/1");
  hash.frame(typeKindName(layout.type.kind));
  hash.frame(toHex(SHA256::hash(arrayRefFromStringRef(key)), true));
  hash.frame(layout.custody ? "1" : "0");
  for (bool allowed : {layout.permissions.copy, layout.permissions.drop,
                       layout.permissions.share, layout.permissions.wire})
    hash.frame(allowed ? "1" : "0");
  hash.frame(std::to_string(layout.leaves.size()));
  for (const auto &leaf : layout.leaves) {
    if (!leaf.data())
      return error("source.formal", "relation schema contains a formal leaf");
    hash.frame(*leaf.data());
  }
  auto fields = [&](ArrayRef<LayoutField> fields) -> Error {
    hash.frame(std::to_string(fields.size()));
    for (const auto &field : fields) {
      hash.frame(field.name);
      hash.frame(std::to_string(field.offset));
      auto child = get(*field.layout);
      if (!child)
        return child.takeError();
      hash.frame(*child);
    }
    return Error::success();
  };
  if (auto error = fields(layout.fields))
    return std::move(error);
  hash.frame(std::to_string(layout.alternatives.size()));
  for (const auto &alternative : layout.alternatives) {
    hash.frame(alternative.name);
    if (auto error = fields(alternative.fields))
      return std::move(error);
  }
  auto digest = hash.finish();
  if (!digest)
    return digest.takeError();
  cache.emplace(&layout, *digest);
  return digest;
}
Layouts::Layouts(const CheckedProject &project, const Limits &limits)
    : definitions(project.declarations()), limits(limits),
      remaining(limits.work) {}
Layouts::Layouts(const ClosedEntry &entry, const Limits &limits)
    : definitions(entry.declarations()), limits(limits),
      remaining(limits.work) {}
Error Layouts::charge(uint64_t n) {
  if (n > remaining)
    return error("source.limit", "layout work limit exceeded");
  remaining -= n;
  return Error::success();
}
Expected<LayoutSlice> Layouts::select(const Declaration &decl,
                                      const SpecificationSelector &selector) {
  const auto &ports = selector.output ? decl.outputs : decl.inputs;
  if (selector.port >= ports.size() || selector.path.size() > limits.typeDepth)
    return error("source.layout", "logical selector is out of bounds");
  uint64_t offset = 0;
  std::shared_ptr<const Layout> selected;
  for (unsigned i = 0; i <= selector.port; ++i) {
    if (auto error = charge(1))
      return std::move(error);
    auto layout = get(ports[i].type);
    if (!layout)
      return layout.takeError();
    if (i == selector.port)
      selected = *layout;
    else
      offset += (*layout)->leaves.size();
  }
  for (auto field : selector.path) {
    if (auto error = charge(1))
      return std::move(error);
    if (selected->custody || selected->type.kind == Type::Kind::Associated ||
        selected->type.kind == Type::Kind::Variant ||
        field >= selected->fields.size())
      return error("source.layout",
                   "logical selector is not a product projection");
    offset += selected->fields[field].offset;
    selected = selected->fields[field].layout;
  }
  if (offset > std::numeric_limits<unsigned>::max())
    return error("source.limit",
                 "logical selector offset exceeds native bounds");
  return LayoutSlice{static_cast<unsigned>(offset), std::move(selected)};
}
const Declaration *Layouts::declaration(StringRef name) const {
  auto found = declarations.find(name.str());
  return found == declarations.end() ? nullptr : found->second;
}
Expected<Type> Layouts::substitute(const Type &type,
                                   const std::map<std::string, Type> &bindings,
                                   unsigned depth) {
  if (depth > limits.typeDepth)
    return error("source.limit", "layout substitution depth exceeded");
  if (auto e = charge(1))
    return e;
  if (type.symbolic) {
    auto found = bindings.find(type.domain);
    if (found != bindings.end()) {
      auto cost =
          typeComplexity(found->second, limits.typeNodes, limits.typeDepth);
      if (!cost)
        return cost.takeError();
      if (auto e = charge(*cost))
        return e;
      return found->second;
    }
  }
  auto cost = typeComplexity(type, limits.typeNodes, limits.typeDepth);
  if (!cost)
    return cost.takeError();
  if (auto e = charge(*cost))
    return e;
  Type result = type;
  for (auto &arg : result.arguments) {
    auto replaced = substitute(arg, bindings, depth + 1);
    if (!replaced)
      return replaced.takeError();
    arg = std::move(*replaced);
  }
  if (!result.dimension.isClosed()) {
    NaturalArithmetic arithmetic(remaining, limits.naturalTerms,
                                 limits.naturalFactors);
    auto normalized = arithmetic.substitute(
        result.dimension, [&](StringRef name) -> const Natural * {
          auto found = bindings.find(name.str());
          return found != bindings.end() &&
                         found->second.kind == Type::Kind::Natural
                     ? &found->second.dimension
                     : nullptr;
        });
    remaining = arithmetic.remainingWork();
    if (!normalized)
      return normalized.takeError();
    result.dimension = std::move(*normalized);
  }
  if (result.kind == Type::Kind::Associated) {
    auto &base = result.arguments.front();
    auto member = StringRef(result.domain).rsplit("::").second;
    result.domain = base.domain + "::" + member.str();
  }
  if (!domainSort(result).empty() && !result.arguments.empty()) {
    const auto &base = result.arguments.front();
    auto member = StringRef(result.domain).rsplit("::").second;
    if (!domainSort(base).empty()) {
      auto resolved = domainMember(base, member);
      if (!resolved)
        return resolved.takeError();
      result = std::move(*resolved);
    } else {
      auto *owner = declaration(base.domain);
      auto *associated = declaration(base.domain + "::" + member.str());
      if (!owner || !associated || associated->abstract ||
          owner->parameters.size() != base.arguments.size())
        return error("source.layout", "associated domain cannot be resolved");
      std::map<std::string, Type> selected;
      for (unsigned i = 0; i < owner->parameters.size(); ++i)
        selected.emplace(owner->parameters[i].atom, base.arguments[i]);
      return substitute(associated->domain, selected, depth + 1);
    }
  }
  if (result.kind == Type::Kind::Natural) {
    result.symbolic = !result.dimension.isClosed();
    if (!result.symbolic)
      result.domain.clear();
  }
  if (result.symbolic || !result.dimension.isClosed())
    return error("source.generic", "unresolved logical layout");
  return result;
}
Expected<std::shared_ptr<const Layout>> Layouts::get(const Type &type) {
  if (auto e = checkLimits(limits))
    return e;
  if (!initialized) {
    for (const auto &decl : definitions) {
      if (auto e = charge(decl.qualifiedName.size() + 1))
        return std::move(e);
      if (!decl.origin)
        declarations.emplace(decl.qualifiedName, &decl);
    }
    initialized = true;
  }
  return build(type, 1);
}
Expected<std::shared_ptr<const Layout>> Layouts::build(const Type &type,
                                                       unsigned depth) {
  if (depth > limits.typeDepth)
    return error("source.limit", "logical layout depth exceeded");
  if (auto e = charge(1))
    return e;
  auto cost = typeComplexity(type, limits.typeNodes, limits.typeDepth);
  if (!cost)
    return cost.takeError();
  if (auto e = charge(*cost))
    return std::move(e);
  auto key = typeIdentity(type);
  if (auto e = charge(key.size()))
    return e;
  auto known = cache.find(key);
  if (known != cache.end())
    return known->second;
  if (type.symbolic || !type.dimension.isClosed())
    return error("source.generic", "layout requires a closed type");
  using K = Type::Kind;
  if (type.kind != K::Array && !type.dimension.terms().empty())
    return error("source.layout", "runtime type has an unexpected dimension");
  if ((type.kind == K::Boolean || type.kind == K::Index ||
       type.kind == K::Unit || type.kind == K::Field ||
       type.kind == K::Group) &&
      !type.arguments.empty())
    return error("source.layout", "scalar type has unexpected arguments");
  if ((type.kind == K::Boolean || type.kind == K::Index ||
       type.kind == K::Unit || type.kind == K::Tuple ||
       type.kind == K::Array) &&
      !type.domain.empty())
    return error("source.layout", "structural type has an unexpected identity");
  if (type.kind == K::Array && type.arguments.size() != 1)
    return error("source.layout", "array requires one element type");
  if (type.kind == K::Associated &&
      (type.arguments.size() != 1 ||
       type.arguments.front().kind != K::Component))
    return error("source.layout", "associated type requires one component");
  auto result = std::make_shared<Layout>();
  result->type = type;
  result->permissions = {true, true, true, true};
  auto *decl = declaration(type.domain);
  if ((type.kind == K::Record &&
       (!decl || decl->kind != Declaration::Kind::Record)) ||
      (type.kind == K::Variant &&
       (!decl || decl->kind != Declaration::Kind::Variant)) ||
      (type.kind == K::Associated &&
       (!decl || decl->kind != Declaration::Kind::Associated || !decl->parent)))
    return error("source.layout", "nominal type declaration differs");
  std::map<std::string, Type> bindings;
  if (decl) {
    const auto *owner = decl;
    const auto *args = &type.arguments;
    if (type.kind == K::Associated) {
      owner = &definitions[decl->parent->index];
      if (type.arguments.front().domain != owner->qualifiedName ||
          decl->abstract)
        return error("source.layout", "associated component identity differs");
      args = &type.arguments.front().arguments;
    }
    if (owner->parameters.size() != args->size())
      return error("source.layout", "nominal static arity differs");
    for (unsigned i = 0; i < args->size(); ++i)
      bindings.emplace(owner->parameters[i].atom, (*args)[i]);
    if (decl->permissions || type.kind == K::Associated)
      result->permissions = decl->permissions.value_or(Permissions{});
    result->custody = (decl->permissions || type.kind == K::Associated) &&
                      !result->permissions.copy;
    if (result->custody) {
      auto slot = "zkl_resource_" + detail::digest(key);
      auto [entry, inserted] = slots.emplace(slot, key);
      if (!inserted && entry->second != key)
        return error("source.symbol",
                     "distinct source types have the same custody identity");
      if (slot.size() > limits.symbolBytes)
        return error("source.limit", "custody identity is too long");
      result->leaves.push_back("resource_unit:" + slot);
    }
  }
  auto addField = [&](StringRef name, const Type &field,
                      std::vector<LayoutField> &fields,
                      std::vector<LayoutLeaf> &leaves) -> Error {
    auto closed = substitute(field, bindings, depth + 1);
    if (!closed)
      return closed.takeError();
    auto layout = build(*closed, depth + 1);
    if (!layout)
      return layout.takeError();
    if (leaves.size() + (*layout)->leaves.size() > limits.aggregateLeaves)
      return error("source.limit", "aggregate layout exceeds leaf limit");
    if (auto e = charge(name.size() + 1))
      return e;
    for (const auto &leaf : (*layout)->leaves)
      if (auto e = charge(leaf.cost()))
        return e;
    result->formal |= (*layout)->formal;
    fields.push_back({name.str(), *layout, unsigned(leaves.size())});
    leaves.insert(leaves.end(), (*layout)->leaves.begin(),
                  (*layout)->leaves.end());
    if ((!decl || !decl->permissions) && type.kind != K::Associated) {
      auto p = (*layout)->permissions;
      result->permissions = {result->permissions.copy && p.copy,
                             result->permissions.drop && p.drop,
                             result->permissions.share && p.share,
                             result->permissions.wire && p.wire};
    }
    return Error::success();
  };
  if (type.kind == K::Boolean)
    result->leaves = {"bool"};
  else if (type.kind == K::Index)
    result->leaves = {"index"};
  else if (type.kind == K::Field)
    result->leaves = {"field:" + type.domain};
  else if (type.kind == K::Group)
    result->leaves = {"group:" + type.domain};
  else if (type.kind == K::Formal) {
    auto formed = formalType(type.domain, type.arguments);
    if (!formed)
      return formed.takeError();
    auto field = builtinLayout(type.arguments[0]);
    if (!field)
      return field.takeError();
    const auto &arity = type.arguments[1].dimension;
    if (!arity.isClosed())
      return error("source.generic", "formal layout requires a closed arity");
    result->formal = true;
    result->permissions = {true, true, false, false};
    result->leaves = {PolynomialLayout{field->identity, arity.closedValue()}};
  } else if (type.kind == K::Builtin) {
    auto native = builtinLayout(type);
    if (!native)
      return native.takeError();
    auto policy = protocol::nativeTypePolicy(*native);
    if (!policy)
      return error("source.builtin",
                   "native data lacks an installed type policy");
    result->leaves = {native->spelling()};
    result->permissions = {protocol::duplicable(*native),
                           protocol::discardable(*native), policy->shared,
                           protocol::nativeMessageData(*native)};
  } else if (type.kind == K::Unit) {
  } else if (type.kind == K::Tuple) {
    for (unsigned i = 0; i < type.arguments.size(); ++i)
      if (auto e = addField(std::to_string(i), type.arguments[i],
                            result->fields, result->leaves))
        return e;
  } else if (type.kind == K::Array) {
    auto size = type.dimension.closedValue();
    if (size > limits.aggregateLeaves)
      return error("source.limit", "array layout exceeds length limit");
    if (size == 0) {
      auto element = substitute(type.arguments.front(), bindings, depth + 1);
      if (!element)
        return element.takeError();
      auto layout = build(*element, depth + 1);
      if (!layout)
        return layout.takeError();
      result->permissions = (*layout)->permissions;
      result->formal = (*layout)->formal;
    }
    for (uint64_t i = 0; i < size; ++i)
      if (auto e = addField(std::to_string(i), type.arguments.front(),
                            result->fields, result->leaves))
        return e;
  } else if (type.kind == K::Record && decl) {
    for (auto &field : decl->fields) {
      if (auto e =
              addField(field.name, field.type, result->fields, result->leaves))
        return e;
      result->permissions.wire &= field.isPublic;
    }
  } else if (type.kind == K::Associated && decl && !decl->abstract) {
    if (auto e =
            addField("value", decl->domain, result->fields, result->leaves))
      return e;
  } else if (type.kind == K::Variant && decl) {
    protocol::VariantDescriptor descriptor{json::Array{"zkc.language", key},
                                           {}};
    for (auto &alt : decl->alternatives) {
      LayoutAlternative logical{alt.name, {}};
      protocol::VariantAlternative native{alt.name, {}};
      std::vector<LayoutLeaf> payload;
      for (auto &field : alt.fields)
        if (auto e = addField(field.name, field.type, logical.fields, payload))
          return e;
      if (result->formal)
        return error("source.formal",
                     "variant payload cannot contain formal values");
      for (const auto &leaf : payload) {
        const auto *data = leaf.data();
        if (!data)
          return error("source.formal",
                       "variant payload cannot contain formal leaves");
        native.payload.push_back(*data);
      }
      result->alternatives.push_back(std::move(logical));
      descriptor.alternatives.push_back(std::move(native));
    }
    auto encoded = protocol::encodeVariant(descriptor);
    if (!encoded)
      return error("source.layout", "variant exceeds native descriptor limits");
    result->leaves.push_back(std::move(*encoded));
  } else
    return error("source.layout", "type has no closed native layout");
  if (result->formal && result->custody)
    return error("source.formal",
                 "formal values cannot have executable custody");
  for (auto &leaf : result->leaves)
    if (const auto *data = leaf.data()) {
      auto bound = protocol::parseBoundType(*data, false);
      if (!bound)
        return bound.takeError();
    }
  std::shared_ptr<const Layout> immutable = result;
  cache.emplace(std::move(key), immutable);
  return immutable;
}
} // namespace zkc::language
