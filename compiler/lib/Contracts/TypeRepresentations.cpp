#include "zkc/Contracts/TypeRepresentations.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Instances.h"
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
  // The applied rows of the native installation that own a single dense
  // child, in declared order. Constructor-wide rows without a child (sequence,
  // variant, resource_unit) select their constructor's default directly.
  namespace physical = installation;
  struct Installed {
    std::vector<std::vector<TypeArgumentPattern>> patterns;
    std::vector<AppliedTypeRepresentation> values;
  };
  static const Installed installed = [] {
    Installed result;
    std::vector<const physical::AppliedRepresentation *> dense;
    for (const auto &row : physical::appliedRepresentations())
      if (row.child)
        dense.push_back(&row);
    for (const auto *row : dense) {
      std::vector<TypeArgumentPattern> patterns;
      for (const auto &pattern : row->arguments) {
        using Kind = physical::ArgumentPattern::Kind;
        switch (pattern.kind) {
        case Kind::Domain:
          patterns.push_back(
              {TypeArgument::domainArgument(pattern.identity), 0, 0});
          break;
        case Kind::Type: {
          // An exact admitted logical type instance.
          const auto &tree = *pattern.type;
          std::string identity =
              tree.arguments.empty() ? "" : tree.arguments.front().identity;
          patterns.push_back({TypeArgument::typeArgument(
                                  BoundType{tree.constructor, identity, {}}),
                              0, 0});
          break;
        }
        case Kind::NatRange:
          patterns.push_back({TypeArgument::naturalArgument(0), pattern.maximum,
                              pattern.minimum});
          break;
        case Kind::Any:
          llvm::report_fatal_error(llvm::Twine("dense representation ") +
                                       row->identity +
                                       " needs exact argument patterns",
                                   false);
        }
      }
      result.patterns.push_back(std::move(patterns));
    }
    for (auto [row, patterns] : llvm::zip(dense, result.patterns))
      result.values.push_back({row->constructor, patterns, row->identity,
                               row->isDefault,
                               BoundType{row->child->kind, row->child->domain,
                                         row->child->representation}});
    if (auto e = validateAppliedTypeRepresentations(result.values))
      llvm::report_fatal_error(
          llvm::Twine("invalid applied representations: ") +
          llvm::toString(std::move(e)));
    return result;
  }();
  return installed.values;
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
