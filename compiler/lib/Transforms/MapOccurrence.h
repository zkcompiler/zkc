#ifndef ZKC_TRANSFORMS_MAPOCCURRENCE_H
#define ZKC_TRANSFORMS_MAPOCCURRENCE_H

#include "LaneRealization.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/MathematicalSelection.h"
#include "zkc/Transforms/MathematicalTrace.h"

namespace zkc::mathematical {
struct SelectedReduction;
/// A representation of one static retained call, never of its declaration.
/// VectorMap is the required endpoint; the two sum forms consume an eligible
/// adjacent original sum. No runtime guard becomes a total-domain premise.
enum class MapPayloadForm { Dot, NumericalSum, NumericalMap, VectorMap };
inline MathematicalSelectionPolicy
mapSelectionPolicy(algebra::MapRealizeOp map,
                   MathematicalSelectionPolicy fallback) {
  if (auto flags = map->getAttrOfType<mlir::ArrayAttr>("policy")) {
    fallback.finiteBulk = mlir::cast<mlir::BoolAttr>(flags[0]).getValue();
    fallback.vectorReductionFusion =
        mlir::cast<mlir::BoolAttr>(flags[1]).getValue();
    fallback.collectFoldFusion =
        mlir::cast<mlir::BoolAttr>(flags[2]).getValue();
  }
  return fallback;
}
using MapEmitter = llvm::function_ref<mlir::Operation *(
    const protocol::BindingApplication &, mlir::ValueRange, mlir::TypeRange,
    llvm::ArrayRef<std::string>)>;

/// Producer preparation only. The independent reader resolves the immutable
/// original helper itself, including its transitive and unused work.
mlir::FailureOr<mlir::OwningOpRef<mlir::func::FuncOp>>
prepareMapFormula(algebra::MapRealizeOp, RealizationWork &);

/// The common payload worker for declaration wrappers and inline occurrences.
/// The emitter owns insertion, binding allocation, bounded sites and work.
llvm::Expected<LaneRealizationResult>
emitMapPayload(algebra::MapRealizeOp, mlir::Block &formula,
               mlir::ValueRange inputs, MapPayloadForm, MapEmitter,
               const SelectedReduction *dot = nullptr);

} // namespace zkc::mathematical
#endif
