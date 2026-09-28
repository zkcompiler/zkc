#ifndef ZKC_MATHEMATICAL_TYPES_H
#define ZKC_MATHEMATICAL_TYPES_H

#include "zkc/Mathematical/Raw.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include <memory>
#include <optional>

namespace zkc::mathematical {

class TypeTable;
class AdmissionBuilder;
struct TypeOwnership;
/// Index into the owning subject's immutable type table. Never a raw type-use
/// ordinal: distinct templates can instantiate to the same mathematical type.
/// Open parameters are positional. Equality compares structural families under
/// a common parameter assignment; it does not identify parameter bindings from
/// different definitions. A consumer must retain the enclosing static scope.
class TypeId {
  const TypeOwnership *owner;
  uint32_t index;
  TypeId(const TypeOwnership *owner, uint32_t index)
      : owner(owner), index(index) {}
  friend class TypeTable;

public:
  uint32_t ordinal() const { return index; }
  bool operator==(TypeId other) const {
    return owner == other.owner && index == other.index;
  }
  bool operator!=(TypeId other) const { return !(*this == other); }
};

struct TypeShape {
  enum class Kind { Nominal, Product, Fin, Vector, Polynomial, Residual };
  Kind kind;
  /// Domain is a manifest reference, meaningful for
  /// nominal/polynomial/residual.
  std::optional<uint32_t> domain;
  std::string constructor;
  std::vector<NormalStatic> statics;
  std::vector<TypeId> elements;
  raw::PolynomialType::Degree degree = raw::PolynomialType::Degree::Individual;
};

/// Expanded constructor count and height. Repeated children count repeatedly;
/// vector lengths and domain-owned leaf payloads are not expanded here.
struct TypeSize {
  uint32_t nodes = 1;
  uint32_t height = 1;
};
inline constexpr uint32_t typeNodeLimit = 65536;
inline constexpr uint32_t typeDepthLimit = 64;

/// Registry validation of a domain-owned mathematical type, including open
/// static parameters. Adapters check legacy closed structural types internally;
/// mathematical storage carries no physical representation metadata. The
/// callback cannot grant protocol admission.
using DomainTypeResolver =
    llvm::function_ref<llvm::Error(const raw::Identity &, const TypeShape &)>;

/// Bounded type expansion and interning. Mutation belongs to the admission
/// builder; admitted subjects expose only a const table. Earlier type
/// references eliminate cycles, including under substitution. TypeIds belong to
/// this table.
class TypeTable {
  friend class AdmissionBuilder;
  TypeTable();
  std::shared_ptr<const TypeOwnership> ownership;
  std::vector<TypeShape> types;
  std::vector<TypeSize> sizes;
  std::map<std::string, TypeId> interned;
  std::map<std::string, TypeId> instances;

  llvm::Expected<TypeId> intern(TypeShape, AdmissionBudget &);
  llvm::Expected<TypeId> expand(const raw::Type &, uint64_t earlier,
                                llvm::ArrayRef<NormalStatic>,
                                const raw::Subject &, DomainTypeResolver,
                                AdmissionBudget &, unsigned depth);

public:
  TypeTable(TypeTable &&) = default;
  TypeTable &operator=(TypeTable &&) = default;
  TypeTable(const TypeTable &) = delete;
  TypeTable &operator=(const TypeTable &) = delete;
  llvm::ArrayRef<TypeShape> all() const { return types; }
  /// Rejects every foreign-table ID, even if its ordinal is in range. IDs are
  /// borrowed handles: retain the owning Subject for their lifetime.
  const TypeShape *get(TypeId type) const;
  const TypeSize *size(TypeId type) const;
  /// The v1 truth type is Fin 2, interpreted with one as true.
  bool isCondition(TypeId type) const;

private:
  llvm::Expected<TypeId> instantiate(const raw::TypeUse &, uint64_t earlier,
                                     llvm::ArrayRef<NormalStatic>,
                                     const raw::Subject &, DomainTypeResolver,
                                     AdmissionBudget &, unsigned depth = 0);
  llvm::Expected<TypeId> formTemplate(uint64_t index, const raw::Subject &,
                                      DomainTypeResolver, AdmissionBudget &);
  llvm::Expected<TypeId> product(llvm::ArrayRef<TypeId>, AdmissionBudget &);
  llvm::Expected<TypeId> fin(NormalStatic count, AdmissionBudget &);
  llvm::Expected<TypeId> vector(TypeId element, NormalStatic count,
                                AdmissionBudget &);
};

} // namespace zkc::mathematical
#endif
