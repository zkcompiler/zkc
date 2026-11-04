#include "zkc/Contracts/TypePolicy.h"
#include "zkc/Contracts/TypeProperties.h"
using namespace llvm;
namespace zkc::protocol {
std::optional<NativeTypeConstructorPolicy>
nativeTypeConstructorPolicy(StringRef kind) {
  // Variants are structural carriers rather than nominal registry entries.
  if (kind == "variant")
    return NativeTypeConstructorPolicy{false, false, true, true};
  const auto *type = typeDeclaration(kind);
  if (!type || !type->nativeLocal)
    return std::nullopt;
  return NativeTypeConstructorPolicy{type->mathematical, type->participants,
                                     type->constructible, type->message};
}
namespace detail {
std::optional<TypePolicyFacts> finishPolicy(const PolicyNode &node,
                                            const PolicyChildren &children) {
  TypePolicyFacts result;
  auto constructor = nativeTypeConstructorPolicy(node.kind);
  bool aggregate = node.kind == "sequence" || node.kind == "variant";
  if (aggregate) {
    result.copy = children.copy;
    result.drop = children.drop;
    result.custody =
        children.copy ? Custody::PrivateImmutable : Custody::Affine;
    result.message = children.message;
    result.protocolPort = children.copy && children.protocolPort;
    result.relation = children.relation;
    result.setup = children.setup;
    if (constructor && children.supported)
      result.native = NativeTypePolicy{children.copy && children.total,
                                       children.copy && children.shared,
                                       !children.copy,
                                       result.protocolPort,
                                       children.message,
                                       children.constructible};
    return result;
  }
  const auto *permissions = typePermissions(node.kind);
  if (!permissions)
    return std::nullopt;
  result.copy = permissions->copy && children.copy;
  result.drop = permissions->drop && children.drop;
  result.custody =
      node.applied ? (permissions->custody == Custody::Affine || !children.copy
                          ? Custody::Affine
                          : Custody::PrivateImmutable)
                   : permissions->custody;
  result.message =
      node.kind == "field_array"
          ? node.fieldArrayFrame
          : !node.applied && nativeMessageAtom(node.kind, node.identity);
  result.setup = setupKey(node.kind).has_value() ||
                 setupCommitment(node.identity) || children.setup;
  result.relation = logicalRelationAtom(node.kind);
  result.protocolPort = children.protocolPort;
  if (constructor && children.supported) {
    bool wire =
        node.kind == "field_array"
            ? node.fieldArrayFrame
            : constructor->shared && !node.applied &&
                  permissions->custody == Custody::PublicValue &&
                  installedDomains().defaultCodec(node.kind, node.identity);
    result.native = NativeTypePolicy{
        constructor->total,
        constructor->shared,
        permissions->custody == Custody::Affine || !children.copy,
        children.protocolPort,
        wire,
        constructor->constructible && children.constructible};
  }
  return result;
}
} // namespace detail
namespace {
struct BoundPolicyAdapter {
  TypeParseBudget &budget;
  bool enter(unsigned depth) {
    if (depth >= 64) {
      budget.limited = true;
      return false;
    }
    return budget.consume();
  }
  bool nominal(const VariantIdentity &identity, unsigned depth = 0) {
    if (!enter(depth))
      return false;
    if (const auto *atom = identity.atom())
      return budget.charge(atom->size());
    for (const auto &child : *identity.tuple())
      if (!nominal(child, depth + 1))
        return false;
    return true;
  }
  std::optional<detail::PolicyNode> head(const BoundType *type) {
    if (!budget.charge(type->kind.size() + type->identity.size()))
      return std::nullopt;
    if (type->variant) {
      if (!nominal(type->variant->nominal))
        return std::nullopt;
      for (const auto &arm : type->variant->alternatives)
        if (!budget.consume() || !budget.charge(arm.label.size()))
          return std::nullopt;
    }
    for (const auto &argument : type->arguments)
      if (!budget.consume() || !budget.charge(argument.domain.size()))
        return std::nullopt;
    return detail::PolicyNode{
        type->kind, type->identity, !type->arguments.empty(),
        type->kind == "field_array" &&
            nativeFieldArrayFrame(type->arguments.front().domain)};
  }
  template <class Include>
  bool children(const BoundType *type, Include include) {
    for (const auto &argument : type->arguments)
      if (argument.kind == TypeArgument::Kind::Type &&
          !include(argument.type.get()))
        return false;
    if (type->variant)
      for (const auto &arm : type->variant->alternatives)
        for (const auto &child : arm.payload)
          if (!include(&child))
            return false;
    return true;
  }
};
std::optional<TypePolicyFacts> readPolicy(StringRef spelling) {
  auto type = parseBoundType(spelling, spelling.contains('@'));
  if (!type) {
    consumeError(type.takeError());
    return std::nullopt;
  }
  return typePolicy(*type);
}
// Called only after the complete tree has passed formation and logical message
// policy. Inspect each physical node once, without rebuilding logical schemas
// or restarting formation/policy budgets at every child.
bool physicalMessage(const BoundType &type) {
  if (type.kind == "sequence" || type.kind == "variant")
    return type.physicalChildren &&
           all_of(*type.physicalChildren, physicalMessage);
  if (type.kind == "field_array")
    return nativeFieldArrayRepresentation(type.arguments[0].domain,
                                          type.arguments[1].natural,
                                          type.representation) &&
           type.physicalChildren && type.physicalChildren->size() == 1 &&
           physicalMessage(type.physicalChildren->front());
  auto selected =
      installedDomains().defaultRepresentation(type.kind, type.identity);
  return (selected && selected->identity == type.representation) ||
         canonicalRepresentation(type.kind, type.identity, type.representation);
}
} // namespace
std::optional<TypePolicyFacts> typePolicy(const BoundType &type,
                                          TypeParseBudget &budget) {
  if (auto e = checkBoundType(type, !type.representation.empty(), &budget)) {
    consumeError(std::move(e));
    return std::nullopt;
  }
  BoundPolicyAdapter adapter{budget};
  return detail::walkTypePolicy(adapter, &type);
}
std::optional<TypePolicyFacts> typePolicy(const BoundType &type) {
  TypeParseBudget budget;
  return typePolicy(type, budget);
}
std::optional<NativeTypePolicy>
nativeTypePolicy(const BoundType &type, unsigned &remaining, bool &limited) {
  if (!type.representation.empty())
    return std::nullopt;
  TypeParseBudget budget;
  budget.remaining = remaining;
  auto facts = typePolicy(type, budget);
  remaining = budget.remaining;
  limited |= budget.limited;
  return facts ? facts->native : std::nullopt;
}
std::optional<NativeTypePolicy> nativeTypePolicy(const BoundType &type) {
  unsigned remaining = 200000;
  bool limited = false;
  return nativeTypePolicy(type, remaining, limited);
}
bool logicalRelationAtom(StringRef kind) {
  return kind == "bool" || kind == "index" || kind == "field" ||
         kind == "group" || kind == "field_array" || kind == "vector" ||
         kind == "matrix" || kind == "groups" || kind == "indices" ||
         kind == "bytes";
}
RelationData logicalRelationData(const BoundType &type, TypeParseBudget &budget,
                                 unsigned depth) {
  if (depth >= 64) {
    budget.limited = true;
    return RelationData::Limit;
  }
  if (!type.representation.empty())
    return RelationData::Unsupported;
  auto facts = typePolicy(type, budget);
  return budget.limited             ? RelationData::Limit
         : facts && facts->relation ? RelationData::Supported
                                    : RelationData::Unsupported;
}
bool programPort(const BoundType &type) {
  auto facts = typePolicy(type);
  return facts && facts->protocolPort;
}
bool duplicable(const BoundType &type) {
  auto facts = typePolicy(type);
  return facts && facts->copy;
}
bool discardable(const BoundType &type) {
  auto facts = typePolicy(type);
  return facts && facts->drop;
}
bool duplicable(StringRef type) {
  auto facts = readPolicy(type);
  return facts && facts->copy;
}
bool discardable(StringRef type) {
  auto facts = readPolicy(type);
  return facts && facts->drop;
}
Custody custody(StringRef type) {
  auto facts = readPolicy(type);
  return facts ? facts->custody : Custody::Unknown;
}
bool nativeSetupType(const BoundType &type) {
  auto facts = typePolicy(type);
  return !facts || facts->setup;
}
bool nativeMessageData(const BoundType &type) {
  auto facts = typePolicy(type);
  return facts && facts->message &&
         (type.representation.empty() || physicalMessage(type));
}
bool nativeFieldArrayWire(const BoundType &type, bool physical) {
  if (type.kind != "field_array" || physical != !type.representation.empty())
    return false;
  return nativeMessageData(type);
}
} // namespace zkc::protocol
