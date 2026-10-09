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
    if (!declaration || !declaration->common ||
        declaration->parameters.empty() ||
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
    for (auto [pattern, parameter] :
         llvm::zip(entry.arguments, declaration->parameters)) {
      switch (parameter.kind) {
      case StaticKind::Type:
        if (pattern.kind != TypeArgument::Kind::Type || pattern.maximum ||
            pattern.minimum || !staticIdentityMatches("Type", pattern.exact))
          return error("representation-pattern");
        break;
      case StaticKind::Domain:
        if (pattern.kind != TypeArgument::Kind::Domain || pattern.maximum ||
            pattern.minimum ||
            !staticIdentityMatches(parameter.sort, pattern.exact))
          return error("representation-pattern");
        break;
      case StaticKind::Nat:
        if (pattern.kind != TypeArgument::Kind::Nat || !pattern.exact.empty() ||
            pattern.minimum > pattern.maximum ||
            !staticIdentityMatches("Nat", std::to_string(pattern.maximum)))
          return error("representation-pattern");
        break;
      }
    }
  }
  for (auto [index, entry] : llvm::enumerate(representations)) {
    for (const auto &other : representations.take_front(index)) {
      if (entry.constructor != other.constructor)
        continue;
      // Intersect closed natural ranges and exact nominal arguments.
      bool overlaps = llvm::all_of(
          llvm::zip(entry.arguments, other.arguments), [](const auto &pair) {
            const auto &[left, right] = pair;
            return left.kind == TypeArgument::Kind::Nat
                       ? left.minimum <= right.maximum &&
                             right.minimum <= left.maximum
                       : left.exact == right.exact;
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
  static const TypeArgumentPattern koalaBearVector[] = {
      {TypeArgument::Kind::Type, "field:koala-bear", 0},
      {TypeArgument::Kind::Nat, {}, 1048576}};
  static const TypeArgumentPattern fieldArray[] = {
      {TypeArgument::Kind::Domain, "bls12-381.fr", 0},
      {TypeArgument::Kind::Nat, {}, 1048576, 0}};
  static const AppliedTypeRepresentation values[] = {
      {"field_array", fieldArray, "arkworks.field-array/0", true},
      {"fixed_vector", koalaBearVector, "plonky3.fixed-vector/0", true}};
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
      if (pattern.kind != argument.kind) {
        matches = false;
        break;
      }
      if (argument.kind == TypeArgument::Kind::Nat)
        matches &= pattern.minimum <= argument.natural &&
                   argument.natural <= pattern.maximum;
      else
        matches &= argument.spelling() == pattern.exact;
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
