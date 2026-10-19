#ifndef ZKC_TRANSFORMS_MATHEMATICALSUPPORT_H
#define ZKC_TRANSFORMS_MATHEMATICALSUPPORT_H
#include "FiniteVerification.h"
#include "zkc/Dialect/Operations.h"
#include "zkc/Transforms/MathematicalSelection.h"
#include "zkc/Transforms/VectorReductions.h"
#include "llvm/ADT/DenseSet.h"
#include <map>
namespace zkc::mathematical {
struct RealizationWork;
struct RealizationTrace;
// Private allowance seam for the same complete staged transaction.
mlir::OwningOpRef<mlir::ModuleOp>
rewriteLocalAlgorithms(mlir::ModuleOp source,
                       MathematicalSelectionPolicy policy,
                       RealizationTrace *trace, RealizationWork &work);
// Bounded derived view: every map formula is admitted, including dead work;
// entries identify exactly a multiplication of two rowwise argument slots in
// scalar operand order. Reduction recipe selection remains separate; no IR or
// expression graph is stored in this view.
mlir::FailureOr<std::map<std::string, std::pair<unsigned, unsigned>>>
describeMapProducts(mlir::ModuleOp module, RealizationTrace *trace = nullptr);
// Private reduction-inventory override. Map admission and installed lane
// recipes are unchanged; the independent reader receives neither inventory.
struct ReductionRecipe;
mlir::LogicalResult
fuseVectorReductions(mlir::ModuleOp module,
                     protocol::AlgorithmExpansionState &state,
                     llvm::ArrayRef<ReductionRecipe> reductions,
                     RealizationTrace *trace = nullptr);
// Read an expanded source map and compare its sum against actual candidate
// instructions. Ordered shape guards and surrounding context belong to the
// caller; this reader receives no producer-selected product slots.
mlir::FailureOr<mlir::Value>
compareMapSum(algebra::MapRealizeOp map, mlir::ValueRange inputs,
              mlir::Value rows, mlir::Operation *&cursor,
              mlir::SymbolTable &candidateSymbols,
              llvm::DenseSet<mlir::Operation *> &bindings, uint64_t &remaining);
// Helpers operate only on an owned candidate whose original module passed
// admission. Work budgets are shared across every selected definition.
mlir::LogicalResult inlineHelpers(mlir::Operation *body, unsigned &remaining,
                                  uint64_t &indices,
                                  mlir::SymbolTableCollection &symbols,
                                  mlir::Operation *lookupRoot = nullptr,
                                  uint64_t *work = nullptr,
                                  OptimizationOutcome *outcome = nullptr);
// Charge every operation of one helper, including the helper itself, its
// terminator and operations no result reaches, to the budgets inlineHelpers
// charges its callees to: one operation, its operand/result slots, and one
// more than those slots of optional work. Callers charge a root helper before
// cloning it so the clone never exceeds what the budgets admit.
mlir::LogicalResult
chargeHelperOperations(mlir::Operation *helper, unsigned &remaining,
                       uint64_t &indices, uint64_t *work = nullptr,
                       OptimizationOutcome *outcome = nullptr);
// Internal rewrite entry used by preparation and participant simplification.
// The caller has already admitted the complete unit.
mlir::LogicalResult simplifyCalculations(mlir::Operation *body);
// Build retained obligations from the original common definition.
mlir::ArrayAttr statementBindings(protocol_ir::MathematicalOp program,
                                  mlir::SymbolTableCollection &symbols);
// Both complete modules have passed ordinary verification, including the
// module-owned calculation-attribution check.
// `batching` selects the calculation schedule the candidate must have.
mlir::LogicalResult verifyMathLowering(protocol_ir::ProtocolModuleOp original,
                                       protocol_ir::ProtocolModuleOp candidate,
                                       bool batching = true);
} // namespace zkc::mathematical
namespace zkc::poly {
mlir::LogicalResult
eliminatePolynomials(mlir::Block &body, uint64_t &remaining,
                     OptimizationOutcome *outcome = nullptr);
}
#endif
