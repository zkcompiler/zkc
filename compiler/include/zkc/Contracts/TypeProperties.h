#ifndef ZKC_CONTRACTS_TYPE_PROPERTIES_H
#define ZKC_CONTRACTS_TYPE_PROPERTIES_H

#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Variant.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringRef.h"

namespace zkc::protocol {
// Classification of an admitted nominal type spelling. Formation and installed
// domain checks remain with admission and the binding registry.
inline llvm::StringRef typeKind(llvm::StringRef type) {
  return type.take_front(type.find_first_of(":<@"));
}
// Native protocol ports admit copyable aggregates recursively.
// This is a logical boundary rule, independent of representation and
// codec availability. The caller supplies a formed, depth-bounded type.
inline bool duplicable(llvm::StringRef type);
inline bool programPort(const BoundType &type) {
  if (type.kind == "variant") {
    auto descriptor =
        decodeVariant(llvm::StringRef(type.spelling()).split('@').first.str());
    if (!descriptor)
      return false;
    for (const auto &arm : descriptor->alternatives)
      for (const auto &leaf : arm.payload) {
        if (!duplicable(leaf))
          return false;
        auto child = parseBoundType(leaf, false);
        if (!child) {
          llvm::consumeError(child.takeError());
          return false;
        }
        if (!programPort(*child))
          return false;
      }
    return true;
  }
  return llvm::all_of(type.arguments, [&](const TypeArgument &argument) {
    return argument.kind != TypeArgument::Kind::Type ||
           programPort(*argument.type);
  });
}
// Native arrays have a frame determined by their complete type. This
// profile fact does not install a codec in older artifact formats.
inline bool nativeFieldArrayWire(const BoundType &type, bool physical = false) {
  return type.kind == "field_array" && type.identity.empty() &&
         type.arguments.size() == 2 &&
         type.arguments[0].kind == TypeArgument::Kind::Domain &&
         type.arguments[0].domain == "bls12-381.fr" &&
         type.arguments[1].kind == TypeArgument::Kind::Nat &&
         type.arguments[1].natural <= 1048576 &&
         (physical ? type.representation == "arkworks.field-array/0"
                   : type.representation.empty());
}
// Complete closed native message grammar. Local copy permission alone is
// insufficient: keys, setup handles and unsupported leaves stay local.
inline bool nativeMessageData(const BoundType &type) {
  if (!type.representation.empty()) {
    auto logical = type;
    logical.representation.clear();
    auto selected = defaultRepresentation(logical);
    if (!selected) {
      llvm::consumeError(selected.takeError());
      return false;
    }
    return *selected == type && nativeMessageData(logical);
  }
  if (type.kind == "sequence")
    return type.arguments.size() == 1 &&
           nativeMessageData(*type.arguments.front().type);
  if (type.kind == "variant") {
    auto descriptor = decodeVariant(type.spelling());
    if (!descriptor)
      return false;
    for (const auto &arm : descriptor->alternatives)
      for (const auto &leaf : arm.payload) {
        auto child = parseBoundType(leaf, false);
        if (!child) {
          llvm::consumeError(child.takeError());
          return false;
        }
        if (!nativeMessageData(*child))
          return false;
      }
    return true;
  }
  return (type.kind == "group" && type.identity == "bn254.gt") ||
         nativeFieldArrayWire(type) ||
         ((type.kind == "bool" || type.kind == "index" ||
           type.kind == "indices") &&
          type.identity.empty()) ||
         ((type.kind == "field" || type.kind == "vector" ||
           type.kind == "matrix") &&
          (type.identity == "bn254.fr" ||
           type.identity == "ristretto255.scalar" ||
           type.identity == "koala-bear" ||
           type.identity == "koala-bear.ext8-binomial3")) ||
         ((type.kind == "group" || type.kind == "groups") &&
          (type.identity == "bn254.g1" || type.identity == "bn254.g2" ||
           type.identity == "ristretto255.group")) ||
         ((type.kind == "field" || type.kind == "vector" ||
           type.kind == "matrix") &&
          type.identity == "bls12-381.fr") ||
         ((type.kind == "group" || type.kind == "groups") &&
          type.identity == "bls12-381.g1") ||
         ((type.kind == "commitment" || type.kind == "proof") &&
          (type.identity == "multilinear.kzg.bls12-381/0" ||
           type.identity == "rows.merkle-keccak256.koala-bear/0" ||
           type.identity ==
               "rows.merkle-keccak256.koala-bear.ext8-binomial3/0"));
}
// Frames introduced by the structured message profile, including standalone
// numeric collections. Existing scalar and fixed-array frames keep their IDs.
inline bool nativeDataFrame(const BoundType &type) {
  return (type.kind == "matrix" || type.kind == "sequence" ||
          type.kind == "variant" || type.kind == "vector" ||
          type.kind == "groups" || type.kind == "indices") &&
         nativeMessageData(type);
}
inline bool nativeSetupType(const BoundType &type) {
  if (type.kind == "prover_key" || type.kind == "verifier_key" ||
      type.identity == "multilinear.kzg.bls12-381/0")
    return true;
  if (type.kind == "variant") {
    auto logical = type;
    logical.representation.clear();
    auto descriptor = decodeVariant(logical.spelling());
    if (!descriptor)
      return true;
    for (const auto &arm : descriptor->alternatives)
      for (const auto &leaf : arm.payload) {
        auto child = parseBoundType(leaf, false);
        if (!child) {
          llvm::consumeError(child.takeError());
          return true;
        }
        if (nativeSetupType(*child))
          return true;
      }
  }
  return llvm::any_of(type.arguments, [&](const TypeArgument &argument) {
    return argument.kind == TypeArgument::Kind::Type &&
           nativeSetupType(*argument.type);
  });
}
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
  if (type.contains('@') && rep != "logical.variant/0")
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
// Use already formed argument trees. Re-stringifying a nested application and
// parsing it for each permission multiplies work at every sequence level.
inline bool boundPermission(const BoundType &type, bool copy) {
  if (type.kind == "variant")
    return variantPermission(type.spelling(), copy);
  const auto *permissions = typePermissions(type.kind);
  return permissions && (copy ? permissions->copy : permissions->drop) &&
         llvm::all_of(type.arguments, [&](const TypeArgument &argument) {
           return argument.kind != TypeArgument::Kind::Type ||
                  boundPermission(*argument.type, copy);
         });
}
inline bool duplicable(const BoundType &type) {
  return boundPermission(type, true);
}
inline bool discardable(const BoundType &type) {
  return boundPermission(type, false);
}
inline Custody custody(llvm::StringRef type) {
  auto kind = typeKind(type);
  if (kind == "variant") {
    auto logical = type.split('@').first;
    if (!decodeVariant(logical.str()) ||
        (type.contains('@') && type.split('@').second != "logical.variant/0"))
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
