#include "zkc/Contracts/TypeRepresentations.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/ErrorHandling.h"

namespace zkc::protocol {
llvm::Error validateAppliedTypeRepresentations(
    llvm::ArrayRef<AppliedTypeRepresentation> representations) {
  for (const auto &entry : representations) {
    const auto *declaration = typeDeclaration(entry.constructor);
    if (!declaration || declaration->parameters.empty() ||
        (declaration->parameters.size() == 1 &&
         declaration->parameters.front().kind == StaticKind::Domain) ||
        entry.arguments.size() != declaration->parameters.size())
      return error("representation-constructor");
    auto identity = entry.representation;
    if (identity.empty() || identity.size() > 256 ||
        !(llvm::isAlpha(identity.front()) || identity.front() == '_') ||
        !llvm::all_of(identity, [](char c) {
          return llvm::isAlnum(c) || c == '_' || c == '.' || c == '-' ||
                 c == '/';
        }))
      return error("representation-identity");
    for (const auto &[pattern, parameter] :
         llvm::zip(entry.arguments, declaration->parameters)) {
      const auto &value = pattern.argument;
      switch (parameter.kind) {
      case StaticKind::Type: {
        if (value.kind != TypeArgument::Kind::Type || !value.type ||
            !value.domain.empty() || value.natural || pattern.maximum ||
            pattern.minimum)
          return error("representation-pattern");
        auto type = parseBoundType(value.type->spelling(), false);
        if (!type) {
          llvm::consumeError(type.takeError());
          return error("representation-pattern");
        }
        if (!(*type == *value.type))
          return error("representation-pattern");
        break;
      }
      case StaticKind::Domain:
        if (value.kind != TypeArgument::Kind::Domain || value.type ||
            value.natural || pattern.maximum || pattern.minimum ||
            !staticIdentityMatches(parameter.sort, value.domain))
          return error("representation-pattern");
        break;
      case StaticKind::Nat:
        if (value.kind != TypeArgument::Kind::Nat || !value.domain.empty() ||
            value.type || value.natural || pattern.minimum > pattern.maximum ||
            pattern.maximum > 1048576)
          return error("representation-pattern");
        break;
      }
    }
    std::vector<std::string> arguments;
    for (const auto &pattern : entry.arguments)
      arguments.push_back(pattern.argument.kind == TypeArgument::Kind::Nat
                              ? std::to_string(pattern.minimum)
                              : pattern.argument.spelling());
    auto logical = applyBoundType(entry.constructor, arguments);
    if (!logical) {
      llvm::consumeError(logical.takeError());
      return error("representation-pattern");
    }
    auto schemas = logicalChildren(*logical);
    if (!schemas)
      return schemas.takeError();
    auto child = parseBoundType(entry.childType.spelling(), true);
    if (!child) {
      llvm::consumeError(child.takeError());
      return error("representation-pattern");
    }
    if (!(*child == entry.childType) || schemas->size() != 1 ||
        !(erasePhysicalType(*child) == schemas->front()))
      return error("representation-pattern");
  }
  for (auto [index, entry] : llvm::enumerate(representations)) {
    for (const auto &other : representations.take_front(index)) {
      if (entry.constructor != other.constructor)
        continue;
      // Intersect closed natural ranges and exact nominal arguments.
      bool overlaps = llvm::all_of(
          llvm::zip(entry.arguments, other.arguments), [](const auto &pair) {
            const auto &[left, right] = pair;
            return left.argument.kind == TypeArgument::Kind::Nat
                       ? left.minimum <= right.maximum &&
                             right.minimum <= left.maximum
                       : left.argument == right.argument;
          });
      if (overlaps && entry.representation == other.representation)
        return error("representation-duplicate");
      if (overlaps && entry.isDefault && other.isDefault)
        return error("representation-default");
    }
  }
  return llvm::Error::success();
}

llvm::ArrayRef<AppliedTypeRepresentation> appliedTypeRepresentations() {
  static const BoundType koalaBear{"field", "koala-bear", {}};
  static const BoundType blsScalar{"field", "bls12-381.fr", {}};
  static const TypeArgumentPattern koalaBearVector[] = {
      {TypeArgument::typeArgument(koalaBear)},
      {TypeArgument::naturalArgument(0), 1048576}};
  static const TypeArgumentPattern fieldArray[] = {
      {TypeArgument::domainArgument("bls12-381.fr")},
      {TypeArgument::naturalArgument(0), 1048576}};
  static const TypeArgumentPattern blsVector[] = {
      {TypeArgument::typeArgument(blsScalar)},
      {TypeArgument::naturalArgument(0), 1048576}};
  static const AppliedTypeRepresentation values[] = {
      {"field_array",
       fieldArray,
       "arkworks.field-array/0",
       true,
       {"field", "bls12-381.fr", "arkworks.fr/0"}},
      {"field_array",
       fieldArray,
       "blst/field-array",
       false,
       {"field", "bls12-381.fr", "blst/fr"}},
      {"fixed_vector",
       blsVector,
       "blst/fixed-vector",
       false,
       {"field", "bls12-381.fr", "blst/fr"}},
      {"fixed_vector",
       koalaBearVector,
       "plonky3.fixed-vector/0",
       true,
       {"field", "koala-bear", "plonky3.koala-bear/0"}}};
  static const bool validated = [] {
    if (auto e = validateAppliedTypeRepresentations(values))
      llvm::report_fatal_error(
          llvm::Twine("invalid applied representations: ") +
          llvm::toString(std::move(e)));
    return true;
  }();
  (void)validated;
  return values;
}

const AppliedTypeRepresentation *
appliedTypeRepresentation(const BoundType &type, llvm::StringRef name) {
  const AppliedTypeRepresentation *selected = nullptr;
  for (const auto &entry : appliedTypeRepresentations()) {
    if (entry.constructor != type.kind ||
        entry.arguments.size() != type.arguments.size() ||
        (name.empty() ? !entry.isDefault : name != entry.representation))
      continue;
    bool matches = true;
    for (auto [pattern, argument] :
         llvm::zip(entry.arguments, type.arguments)) {
      if (pattern.argument.kind != argument.kind) {
        matches = false;
        break;
      }
      if (argument.kind == TypeArgument::Kind::Nat)
        matches &= pattern.minimum <= argument.natural &&
                   argument.natural <= pattern.maximum;
      else
        matches &= argument == pattern.argument;
    }
    if (!matches)
      continue;
    if (selected)
      return nullptr;
    selected = &entry;
  }
  return selected;
}
} // namespace zkc::protocol
