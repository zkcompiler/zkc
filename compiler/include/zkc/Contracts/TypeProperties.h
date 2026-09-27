#ifndef ZKC_CONTRACTS_TYPE_PROPERTIES_H
#define ZKC_CONTRACTS_TYPE_PROPERTIES_H

#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Variant.h"
#include "llvm/ADT/StringRef.h"

namespace zkc::protocol {
// Classification of an admitted nominal type spelling. Formation and installed
// domain checks remain with admission and the binding registry.
inline llvm::StringRef typeKind(llvm::StringRef type) {
  return type.take_front(type.find_first_of(":<@"));
}
inline bool duplicable(llvm::StringRef type);
inline bool discardable(llvm::StringRef type);
inline bool applicationPermission(llvm::StringRef type, bool copy) {
  auto parsed = parseBoundType(type.split('@').first, false);
  if (!parsed) {
    llvm::consumeError(parsed.takeError());
    return false;
  }
  for (const auto &argument : parsed->arguments)
    if (argument.kind == TypeArgument::Kind::Type &&
        !(copy ? duplicable(argument.type->spelling())
               : discardable(argument.type->spelling())))
      return false;
  return true;
}
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
  const auto *permissions = typePermissions(kind);
  if (type.contains('<')) {
    auto parsed = parseBoundType(type.split('@').first, false);
    if (!parsed) {
      llvm::consumeError(parsed.takeError());
      return Custody::Unknown;
    }
    if (!permissions)
      return Custody::Unknown;
    // Element serialization does not confer a container codec.
    return permissions->custody == Custody::Affine ||
                   !applicationPermission(type, true)
               ? Custody::Affine
               : Custody::PrivateImmutable;
  }
  return permissions ? permissions->custody : Custody::Unknown;
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
  const auto *permissions = typePermissions(typeKind(type));
  return permissions && permissions->drop &&
         (!type.contains('<') || applicationPermission(type, false));
}
// Aliasing immutable local custody does not authorize cross-role replay.
// Logical resource units may be dropped, but never aliased.
inline bool duplicable(llvm::StringRef type) {
  if (typeKind(type) == "variant")
    return variantPermission(type, true);
  const auto *permissions = typePermissions(typeKind(type));
  return permissions && permissions->copy &&
         (!type.contains('<') || applicationPermission(type, true));
}
} // namespace zkc::protocol
#endif
