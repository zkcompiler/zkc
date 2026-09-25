#ifndef ZKC_PROTOCOL_TYPE_PROPERTIES_H
#define ZKC_PROTOCOL_TYPE_PROPERTIES_H

#include "zkc/Protocol/Variant.h"
#include "llvm/ADT/StringRef.h"

namespace zkc::protocol {
// Classification of an admitted nominal type spelling. Formation and installed
// domain checks remain with admission and the binding registry.
inline llvm::StringRef typeKind(llvm::StringRef type) {
  return type.split('@').first.split(':').first;
}
inline bool duplicable(llvm::StringRef type);
inline bool discardable(llvm::StringRef type);
inline bool variantPermission(llvm::StringRef type, bool copy) {
  auto [logical, rep] = type.split('@');
  if (type.contains('@') && rep != "logical.variant/1")
    return false;
  auto descriptor = decodeVariant(logical.str());
  if (!descriptor)
    return false;
  for (const auto &arm : descriptor->alternatives)
    for (const auto &leaf : arm.payload)
      if (!(copy ? duplicable(leaf) : discardable(leaf)))
        return false;
  return true;
}
enum class Custody { Unknown, PublicValue, PrivateImmutable, Affine };
inline Custody custody(llvm::StringRef type) {
  auto kind = typeKind(type);
  if (kind == "variant") {
    auto logical = type.split('@').first;
    if (!decodeVariant(logical.str()) ||
        (type.contains('@') && type.split('@').second != "logical.variant/1"))
      return Custody::Unknown;
    return variantPermission(type, true) ? Custody::PrivateImmutable
                                         : Custody::Affine;
  }
  if (kind == "transcript" || kind == "rng" || kind == "nonce" ||
      kind == "capability" || kind == "resource_unit")
    return Custody::Affine;
  if (kind == "opening_state" || kind == "opening_states" ||
      kind == "prover_key" || kind == "verifier_key")
    return Custody::PrivateImmutable;
  if (kind == "index" || kind == "indices" || kind == "matrix" ||
      kind == "vector" || kind == "polynomial" || kind == "field" ||
      kind == "table" || kind == "point" || kind == "round" || kind == "bool" ||
      kind == "commitment" || kind == "commitments" || kind == "proof" ||
      kind == "scalar" || kind == "group" || kind == "groups")
    return Custody::PublicValue;
  return Custody::Unknown;
}
inline bool hasTypeProperties(llvm::StringRef type) {
  return custody(type) != Custody::Unknown;
}
inline bool affine(llvm::StringRef type) {
  return custody(type) == Custody::Affine;
}
// PublicValue describes a codec, not an information-flow authorization to send
// a secret value. Ownership and disclosure checks are independent.
inline bool serializable(llvm::StringRef type) {
  return custody(type) == Custody::PublicValue;
}
inline bool discardable(llvm::StringRef type) {
  if (typeKind(type) == "variant")
    return variantPermission(type, false);
  auto c = custody(type);
  return typeKind(type) == "resource_unit" || c == Custody::PublicValue ||
         c == Custody::PrivateImmutable;
}
// Aliasing immutable local custody does not authorize cross-role replay.
// Logical resource units may be dropped, but never aliased.
inline bool duplicable(llvm::StringRef type) {
  if (typeKind(type) == "variant")
    return variantPermission(type, true);
  auto c = custody(type);
  return c == Custody::PublicValue || c == Custody::PrivateImmutable;
}
} // namespace zkc::protocol
#endif
