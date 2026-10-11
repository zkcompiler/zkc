#ifndef ZKC_TRANSFORMS_LANEREALIZATION_H
#define ZKC_TRANSFORMS_LANEREALIZATION_H

#include "mlir/IR/ValueRange.h"
#include "mlir/Support/LogicalResult.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/STLFunctionalExtras.h"

namespace zkc::mathematical {
/// One admitted scalar formula input, represented once or once per lane.
/// Access/admission analysis supplies these bindings; it does not authorize
/// movement of ordered computations into the formula.
struct LaneInput {
  mlir::Value value;
  bool lanes = false;
};
using LaneEmitter =
    llvm::function_ref<mlir::Value(llvm::StringRef, mlir::ValueRange,
                                   mlir::Type, llvm::ArrayRef<std::string>)>;

/// Realize a field-ring payload using the same scalar/broadcast/packed rules
/// for maps and finite collections. Structural sharing is checked through
/// RingSharing. The caller owns ordered admission and binding construction;
/// an independent semantic reader must check the actual candidate afterwards.
mlir::FailureOr<mlir::Value>
realizeLanes(mlir::Block &formula,
             const llvm::DenseMap<mlir::Value, LaneInput> &inputs,
             mlir::Type vector, mlir::Value length, LaneEmitter emit);
} // namespace zkc::mathematical
#endif
