#ifndef ZKC_LANGUAGE_TYPES_H
#define ZKC_LANGUAGE_TYPES_H
#include "zkc/Language/Natural.h"
#include <optional>
#include <string>
#include <vector>

namespace zkc::language {
struct Permissions {
  bool copy = false, drop = false, share = false, wire = false;
  bool operator==(const Permissions &b) const {
    return copy == b.copy && drop == b.drop && share == b.share &&
           wire == b.wire;
  }
  bool includes(const Permissions &b) const {
    return (!b.copy || copy) && (!b.drop || drop) && (!b.share || share) &&
           (!b.wire || wire);
  }
};
/// A resolved source term. Natural, Domain, Asset and Component are static
/// sorts and cannot form runtime values. Parameters carry
/// declaration-qualified atom identities. Nominal arguments include phantom
/// parameters; representation is not identity.
struct Type {
  enum class Kind {
    Boolean,
    Field,
    Group,
    Index,
    Unit,
    Tuple,
    Array,
    Record,
    Variant,
    Parameter,
    Associated,
    Natural,
    Component,
    Builtin,
    Formal,
    Domain,
    /// A capture-local immutable asset (a ring arena or a relation bundle).
    /// The domain is the canonical asset identity when closed and the
    /// parameter atom when symbolic; the sort is Ring or Bundle.
    Asset
  };
  Kind kind = Kind::Boolean;
  std::string domain;
  /// Catalog sort for static-only domains and asset sort for assets; Field and
  /// Group use their own kinds.
  std::string sort;
  std::vector<Type> arguments;
  Natural dimension;
  bool symbolic = false;
  Permissions assumptions;
  Type() = default;
  Type(Kind kind, std::string domain = {})
      : kind(kind), domain(std::move(domain)) {}
  bool operator==(const Type &b) const {
    if (kind == Kind::Natural && b.kind == Kind::Natural)
      return dimension == b.dimension;
    return kind == b.kind && domain == b.domain && sort == b.sort &&
           arguments == b.arguments && dimension == b.dimension &&
           symbolic == b.symbolic;
  }
  bool operator!=(const Type &b) const { return !(*this == b); }
};
/// Canonical source term for an admitted catalog domain sort and identity.
/// Only this constructor and assetType set Type::sort.
Type domainType(llvm::StringRef sort, llvm::StringRef identity);
llvm::StringRef domainSort(const Type &);
/// Asset sorts name captured mathematics, never installed catalog identities.
bool isAssetSort(llvm::StringRef);
/// Canonical source term for a captured asset of the given sort. The identity
/// is the canonical definition identity of the captured asset.
Type assetType(llvm::StringRef sort, llvm::StringRef identity);
/// The asset sort of an asset term; empty for every other kind.
llvm::StringRef assetSort(const Type &);
bool isStaticOnly(const Type &);
llvm::StringRef typeKindName(Type::Kind);
std::string spelling(const Type &);
/// Injective internal key; source-facing spelling is deliberately separate.
std::string typeIdentity(const Type &);
/// Bound traversal and expanded identity material before copying a term.
llvm::Expected<uint64_t> typeComplexity(const Type &, uint64_t nodes,
                                        uint64_t depth);
} // namespace zkc::language
#endif
