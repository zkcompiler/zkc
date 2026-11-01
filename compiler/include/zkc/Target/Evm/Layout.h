#ifndef ZKC_TARGET_EVM_LAYOUT_H
#define ZKC_TARGET_EVM_LAYOUT_H

#include "mlir/IR/TypeRange.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/Error.h"
#include <memory>
#include <optional>

namespace zkc::evm {
struct LaneSlice {
  unsigned first, count;
};
struct SignatureLayout {
  llvm::SmallVector<mlir::Type> lanes;
  llvm::SmallVector<LaneSlice> values;
};
struct FieldLayout {
  algebra::FieldType type, base;
  llvm::APInt modulus{256, 0};
  unsigned degree = 1;
  llvm::APInt beta{256, 0};
  uint64_t coefficientBytes() const { return uint64_t(degree) * 32; }
};
struct CollectionLayout {
  enum class Storage { FieldCoefficients, LaneCells, PackedBytes };
  mlir::Type element;
  Storage storage;
  uint64_t strideBytes;
};
struct ValueLayout {
  enum class Kind {
    Boolean,
    Index,
    Field,
    FieldVector,
    Indices,
    Bytes,
    Sequence,
    Variant,
    FieldArray,
    FixedVector,
    Root,
    Path
  };
  mlir::Type logical;
  Kind kind;
  llvm::SmallVector<mlir::Type, 2> lanes;
  std::optional<CollectionLayout> collection;
  uint64_t laneCellBytes() const { return uint64_t(lanes.size()) * 32; }
};
/// Read-only consumer of native logical types and installed domain facts.
/// Descriptors are immutable, cache-owned and address-stable. This grants no
/// wire permission, codec, mathematical totality or execution authority.
class NativeLayouts {
public:
  explicit NativeLayouts(mlir::MLIRContext &);
  ~NativeLayouts();
  llvm::Expected<const ValueLayout *> get(mlir::Type);
  llvm::Expected<const FieldLayout *> field(algebra::FieldType);
  llvm::Expected<SignatureLayout> signature(mlir::TypeRange);
  llvm::Expected<SignatureLayout> payload(data::VariantType,
                                          uint32_t alternative);

private:
  struct Storage;
  std::unique_ptr<Storage> storage;
};
} // namespace zkc::evm
#endif
