#ifndef ZKC_TRANSFORMS_LANEREALIZATION_H
#define ZKC_TRANSFORMS_LANEREALIZATION_H

#include "NativeBindingApplication.h"
#include "mlir/IR/ValueRange.h"
#include "mlir/Support/LogicalResult.h"
#include "zkc/Contracts/Mathematical.h"
#include "zkc/Contracts/Numerical.h"
#include "zkc/Support/OptimizationOutcome.h"
#include "zkc/Transforms/MathematicalSelection.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <optional>
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
using LaneEmitter = llvm::function_ref<mlir::Value(
    llvm::StringRef, mlir::ValueRange, mlir::Type,
    llvm::ArrayRef<mlir::Attribute>)>;

enum class LaneRealizationStatus { Realized, Unsupported, Capacity };
struct LaneRealizationResult {
  LaneRealizationStatus status;
  mlir::Value value;
  std::string reason;
  OptimizationOutcome outcome = OptimizationOutcome::success();
};

/// An admitted source formula, independent of any executable choice. The
/// borrowed block and values must outlive emission. The input inventory retains
/// unused slots in deterministic source order; expression sharing is checked.
struct LaneFormula {
  ring::Expression expression;
  mlir::Block *source;
  llvm::DenseMap<mlir::Value, LaneInput> bindings;
  llvm::DenseMap<mlir::Value, uint32_t> meanings;
  llvm::DenseSet<mlir::Value> live;
  llvm::SmallVector<mlir::Value> terms;
  llvm::SmallVector<LaneInput> slots;
  MathematicalIdentity combine;
};
struct LaneFormulaResult {
  LaneRealizationStatus status;
  std::optional<LaneFormula> formula;
  std::string reason;
  OptimizationOutcome outcome = OptimizationOutcome::success();
};
/// Construct a single-output Ring formula after admitting the entire source.
/// Multiple selected terms are combined by admitted field addition or
/// multiplication, as supplied by associative accumulator extraction.
llvm::Expected<LaneFormulaResult>
admitLaneFormula(mlir::Block &, const llvm::DenseMap<mlir::Value, LaneInput> &,
                 mlir::Type vector, uint64_t *remaining,
                 const MathematicalRecipes &, mlir::Value output = {},
                 mlir::ValueRange additionalTerms = {},
                 MathematicalIdentity combine = MathematicalIdentity::FieldAdd);
llvm::Expected<LaneRealizationResult>
emitVectorLanes(const LaneFormula &, mlir::Type vector, mlir::Value rows,
                const MathematicalRecipes &, LaneEmitter);
using NumericalEmitter = llvm::function_ref<mlir::Value(
    const NativeBindingApplication &, mlir::ValueRange, mlir::Type,
    llvm::ArrayRef<mlir::Attribute>)>;
enum class LaneResultMode { Map, Sum, Product };
/// Row-bearing maps use checked Tensor/Linalg realization; selected sums also
/// fuse their reduction. Construction charges the supplied shared work budget.
/// Capacity declines emit nothing. The caller can use the same admitted
/// formula for a vector alternative, without repeating optional analysis.
llvm::Expected<LaneRealizationResult>
emitNumericalLanes(const LaneFormula &, mlir::Type vector, mlir::Value rows,
                   LaneResultMode, NumericalEmitter,
                   uint64_t *remaining = nullptr);

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
