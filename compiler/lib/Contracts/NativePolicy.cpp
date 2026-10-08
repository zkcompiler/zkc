#include "zkc/Contracts/NativePolicy.h"
#include "zkc/Contracts/TypeProperties.h"
#include "llvm/ADT/StringSwitch.h"
using namespace llvm;
namespace zkc::protocol {
std::optional<NativeTypeConstructorPolicy>
nativeTypeConstructorPolicy(StringRef kind) {
  bool total = kind == "bool" || kind == "field" || kind == "group" ||
               kind == "field_array" || kind == "index" || kind == "indices" ||
               kind == "vector" || kind == "matrix" || kind == "groups";
  bool shared =
      total ||
      llvm::StringSwitch<bool>(kind)
          .Cases({"index", "indices", "vector", "matrix"}, true)
          .Cases({"polynomial", "table", "point", "round"}, true)
          .Cases({"groups", "commitment", "commitments", "proof"}, true)
          .Default(false);
  bool local = llvm::StringSwitch<bool>(kind)
                   .Cases({"opening_states", "prover_key", "verifier_key",
                           "opening_state"},
                          true)
                   .Cases({"rng", "nonce", "transcript", "resource_unit"}, true)
                   .Cases({"fixed_vector", "variant"}, true)
                   .Default(false);
  if (!shared && !local && kind != "sequence")
    return std::nullopt;
  return NativeTypeConstructorPolicy{total, shared};
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
       protocolPort = true;
  auto include = [&](const protocol::BoundType &child) {
    bool childCopy = false;
    auto facts = policy(child, depth + 1, remaining, limited, childCopy);
    if (!facts)
      return false;
    childrenCopy &= childCopy;
    childrenTotal &= facts->total;
    childrenShared &= facts->shared;
    protocolPort &= facts->protocolPort;
    return true;
  };
  for (const auto &argument : type.arguments)
    if (argument.kind == protocol::TypeArgument::Kind::Type &&
        !include(*argument.type))
      return std::nullopt;
  if (kind == "sequence") {
    copy = childrenCopy;
    return NativeTypePolicy{copy && childrenTotal, copy && childrenShared,
                            !copy, copy && protocolPort,
                            protocol::nativeMessageData(type)};
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
    return NativeTypePolicy{copy && childrenTotal, copy && childrenShared,
                            !copy, copy && protocolPort,
                            protocol::nativeMessageData(type)};
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
  return NativeTypePolicy{total, shared, affine, protocolPort, wire};
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
  return type.kind == "bool" || type.kind == "index" || type.kind == "field" ||
                 type.kind == "group" || type.kind == "field_array" ||
                 type.kind == "vector" || type.kind == "matrix" ||
                 type.kind == "groups" || type.kind == "indices"
             ? R::Supported
             : R::Unsupported;
}

} // namespace zkc::protocol
