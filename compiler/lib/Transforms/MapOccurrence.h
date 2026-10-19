#ifndef ZKC_TRANSFORMS_MAPOCCURRENCE_H
#define ZKC_TRANSFORMS_MAPOCCURRENCE_H

#include "LaneRealization.h"
#include "MathematicalComparison.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/MathematicalTrace.h"

namespace zkc::protocol {
class AlgorithmExpansionState;
}
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

/// Read ordered every-column guards followed by the actual payload. `end` is
/// an exclusive boundary independently identified by the enclosing context;
/// `output` names the actual result when known; an empty value permits any
/// matching available result whose use the enclosing context must check.
/// No cursor/binding update is published on failure. Spent work stays spent.
mlir::FailureOr<mlir::Value>
readMapPayload(algebra::MapRealizeOp, mlir::ValueRange inputs, bool sum,
               mlir::Operation *&cursor, mlir::Operation *end,
               mlir::Value output, mlir::SymbolTable &,
               llvm::DenseSet<mlir::Operation *> &bindings,
               uint64_t &requiredWork, uint64_t &optionalWork,
               VerificationDecision &outcome);

/// Exact original pair eligibility, including persisted policy, adjacency,
/// single use, contract, nominal field and both source and requested pins.
algebra::MapRealizeOp eligibleMapSum(
    local::ApplyOp, mlir::SymbolTable &, MathematicalSelectionPolicy,
    llvm::ArrayRef<std::pair<std::string, std::string>> selections = {});
// Standalone checked transforms used by internal clients and focused tests.
// Production selection composes the occurrence emitter and reader directly.
/// Optional late multiply-map/sum fusion on an immutable logical subject after
/// ordinary algorithm expansion. Share expansion allowances across attempts.
/// The selector may decline individual eligible calls in the private candidate;
/// it cannot enable a disabled family or replace a fixed reduction binding.
/// Call pointers are synchronous observations, never persistent identities or
/// correspondence evidence. A null selector accepts every eligible pair.
/// The returned candidate has passed independent guard/payload readback.
mlir::OwningOpRef<mlir::ModuleOp> fuseRetainedMapReductions(
    mlir::ModuleOp source, MathematicalSelectionPolicy policy,
    protocol::AlgorithmExpansionState &state, RealizationTrace *trace = nullptr,
    llvm::function_ref<bool(mlir::Operation *)> select = nullptr);
/// Independently read a selected late candidate against its immutable subject.
/// Unselected calls, declarations, helper closures and surrounding code stay
/// exact. Selection callbacks and producer occurrence records are not evidence.
mlir::LogicalResult
verifyRetainedMapReductionsPreserved(mlir::ModuleOp original,
                                     mlir::ModuleOp candidate,
                                     MathematicalSelectionPolicy policy);

} // namespace zkc::mathematical
#endif
