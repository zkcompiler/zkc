#ifndef ZKC_LANGUAGE_VALUEPLACEMENT_H
#define ZKC_LANGUAGE_VALUEPLACEMENT_H

#include "llvm/ADT/ArrayRef.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <string>
#include <utility>
#include <variant>
#include <vector>

namespace zkc::language {
/// Distinct local components, not a proof that their values agree.
struct DataPlacement {
  std::vector<unsigned> roles;
  bool operator==(const DataPlacement &other) const {
    return roles == other.roles;
  }
};
struct OraclePlacement {
  unsigned holder;
  std::vector<unsigned> receivers;
  bool operator==(const OraclePlacement &other) const {
    return holder == other.holder && receivers == other.receivers;
  }
};
struct ValuePlacement;
/// A logical product has no aggregate availability or oracle holder.
/// Its schema supplies field names, visibility, types and custody restrictions.
struct ProductPlacement {
  /// Exact kinded nominal instance identity, including phantom arguments.
  std::string instance;
  /// Nominal: injective substitution in declaration telescope order, never
  /// sorted. Structural: canonical participation scope derived from children.
  std::vector<unsigned> arguments;
  /// Declaration order, including children with no native storage. A fixed
  /// logical array retains one element-schema child, independently of extent.
  std::vector<ValuePlacement> fields;
  bool operator==(const ProductPlacement &) const;
};
struct ValuePlacement {
  std::variant<DataPlacement, OraclePlacement, ProductPlacement> value;
  ValuePlacement(DataPlacement data) : value(std::move(data)) {}
  ValuePlacement(OraclePlacement oracle) : value(std::move(oracle)) {}
  ValuePlacement(ProductPlacement product) : value(std::move(product)) {}
  bool operator==(const ValuePlacement &other) const {
    return value == other.value;
  }
  bool operator!=(const ValuePlacement &other) const {
    return !(*this == other);
  }
};
inline bool ProductPlacement::operator==(const ProductPlacement &other) const {
  return instance == other.instance && arguments == other.arguments &&
         fields == other.fields;
}

/// Validate the finite placement tree and debit the shared work budget. Schema
/// agreement (including each field's type and role formula) is a separate
/// check.
llvm::Error validatePlacement(const ValuePlacement &, unsigned participants,
                              uint64_t &remaining, unsigned maximumDepth);
/// Apply an injective source-roster to destination-roster substitution. Set
/// components are canonicalized; product arguments preserve telescope order.
llvm::Expected<ValuePlacement>
substitutePlacement(const ValuePlacement &, llvm::ArrayRef<unsigned> mapping,
                    unsigned participants, uint64_t &remaining,
                    unsigned maximumDepth);
/// Participation summary only. A product's summary grants no field access and
/// establishes no agreement between role-local data components.
std::vector<unsigned> placementRoles(const ValuePlacement &);
} // namespace zkc::language
#endif
