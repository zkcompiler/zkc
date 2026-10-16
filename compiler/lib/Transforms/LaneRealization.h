#ifndef ZKC_TRANSFORMS_LANEREALIZATION_H
#define ZKC_TRANSFORMS_LANEREALIZATION_H

#include "mlir/IR/ValueRange.h"
#include "mlir/Support/LogicalResult.h"
#include "zkc/Support/OptimizationOutcome.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <string>

namespace zkc::mathematical {
struct MathematicalRecipes;
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

enum class LaneRealizationStatus { Realized, Unsupported, Capacity };
struct LaneRealizationResult {
  LaneRealizationStatus status;
  mlir::Value value;
  std::string reason;
  OptimizationOutcome outcome = OptimizationOutcome::success();
};

/// Realize a field-ring payload using the same scalar/broadcast/packed rules
/// for maps and finite collections. Structural sharing is checked through
/// RingSharing. The caller owns ordered admission and binding construction;
/// an independent semantic reader must check the actual candidate afterwards.
/// Unsupported/capacity results emit nothing, so an optional caller can retain
/// its ordered implementation. Errors indicate a failed construction/check,
/// never permission to accept or publish a partly emitted candidate. The
/// optional work budget belongs to the enclosing selection stage, not each
/// formula. Required maps already charge their complete expanded helpers.
/// Use the same immutable recipe inventory as selection; emission does not
/// consult the global inventory or grant the independent reader new premises.
/// A selected output realizes its dependency slice after admitting the whole
/// body. Unbound arguments (such as a reduction's state) cannot enter that
/// slice.
llvm::Expected<LaneRealizationResult>
realizeLanes(mlir::Block &formula,
             const llvm::DenseMap<mlir::Value, LaneInput> &inputs,
             mlir::Type vector, mlir::Value length, uint64_t *remaining,
             const MathematicalRecipes &recipes, LaneEmitter emit,
             mlir::Value output = {});
} // namespace zkc::mathematical
#endif
