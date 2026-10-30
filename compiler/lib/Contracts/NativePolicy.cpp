#include "zkc/Contracts/NativePolicy.h"
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
namespace {
std::optional<NativeTypePolicy> policy(const protocol::BoundType &type,
                                       unsigned depth, unsigned &remaining,
                                       bool &limited, bool &copy) {
  if (!remaining || depth > 64) {
    limited = true;
    return std::nullopt;
  }
  --remaining;
  StringRef kind = type.kind;
  auto constructor = nativeTypeConstructorPolicy(kind);
  if (!constructor)
    return std::nullopt;
  bool total = constructor->total, shared = constructor->shared;
  // Accumulate custody and boundary facts once per child. Do not stringify
  // and reparse every subtree through the generic custody helpers.
  bool childrenCopy = true, childrenTotal = true, childrenShared = true,
       protocolPort = true, childrenConstructible = true;
  auto include = [&](const protocol::BoundType &child) {
    bool childCopy = false;
    auto facts = policy(child, depth + 1, remaining, limited, childCopy);
    if (!facts)
      return false;
    childrenCopy &= childCopy;
    childrenTotal &= facts->total;
    childrenShared &= facts->shared;
    childrenConstructible &= facts->constructible;
    protocolPort &= facts->protocolPort;
    return true;
  };
  for (const auto &argument : type.arguments)
    if (argument.kind == protocol::TypeArgument::Kind::Type &&
        !include(*argument.type))
      return std::nullopt;
  if (kind == "sequence") {
    copy = childrenCopy;
    return NativeTypePolicy{copy && childrenTotal,
                            copy && childrenShared,
                            !copy,
                            copy && protocolPort,
                            protocol::nativeMessageData(type),
                            childrenConstructible};
  }
  if (kind == "variant") {
    auto descriptor = protocol::decodeVariant(type.spelling());
    if (!descriptor)
      return std::nullopt;
    for (const auto &arm : descriptor->alternatives)
      for (const auto &leaf : arm.payload) {
        auto parsed = protocol::parseBoundType(leaf, false);
        if (!parsed) {
          consumeError(parsed.takeError());
          return std::nullopt;
        }
        if (!include(*parsed))
          return std::nullopt;
      }
    copy = childrenCopy;
    return NativeTypePolicy{copy && childrenTotal,
                            copy && childrenShared,
                            !copy,
                            copy && protocolPort,
                            protocol::nativeMessageData(type),
                            childrenConstructible};
  }
  const auto *permissions = protocol::typePermissions(kind);
  if (!permissions)
    return std::nullopt;
  copy = permissions->copy && childrenCopy;
  bool affine =
      permissions->custody == protocol::Custody::Affine || !childrenCopy;
  // A structural application does not inherit its nominal head's wire codec.
  bool wire = shared && type.arguments.empty() &&
              permissions->custody == protocol::Custody::PublicValue &&
              !protocol::defaultCodec(type).empty();
  if (kind == "field_array")
    wire = protocol::nativeFieldArrayWire(type);
  return NativeTypePolicy{
      total,  shared,
      affine, protocolPort,
      wire,   constructor->constructible && childrenConstructible};
}
} // namespace
std::optional<NativeTypePolicy>
nativeTypePolicy(const BoundType &type, unsigned &remaining, bool &limited) {
  bool copy = false;
  return policy(type, 0, remaining, limited, copy);
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
  using R = RelationData;
  if (depth > 64 || !budget.consume())
    return R::Limit;
  if (!type.representation.empty())
    return R::Unsupported;
  if (type.kind == "variant") {
    auto descriptor = decodeVariant(type.spelling(), depth, &budget);
    if (!descriptor)
      return budget.remaining ? R::Unsupported : R::Limit;
    for (const auto &arm : descriptor->alternatives)
      for (const auto &leaf : arm.payload) {
        if (depth == 64)
          return R::Limit;
        auto child = parseBoundType(leaf, false, depth + 1, &budget);
        if (!child) {
          consumeError(child.takeError());
          return budget.remaining ? R::Unsupported : R::Limit;
        }
        auto result = logicalRelationData(*child, budget, depth + 1);
        if (result != R::Supported)
          return result;
      }
    return R::Supported;
  }
  if (type.kind == "sequence") {
    for (const auto &argument : type.arguments)
      if (argument.kind == TypeArgument::Kind::Type) {
        auto result = logicalRelationData(*argument.type, budget, depth + 1);
        if (result != R::Supported)
          return result;
      }
    return R::Supported;
  }
  // Copyable keys and private resources are not immutable relation data.
  return logicalRelationAtom(type.kind) ? R::Supported : R::Unsupported;
}

} // namespace zkc::protocol
