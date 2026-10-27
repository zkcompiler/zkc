#ifndef ZKC_TRANSFORMS_MATHEMATICALSUPPORT_H
#define ZKC_TRANSFORMS_MATHEMATICALSUPPORT_H
#include "FiniteVerification.h"
#include "zkc/Dialect/Operations.h"
#include "zkc/Transforms/MathematicalSelection.h"
#include "llvm/ADT/DenseSet.h"
namespace zkc::mathematical {
struct RealizationWork;
struct RealizationTrace;
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
