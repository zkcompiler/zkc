#ifndef ZKC_TRANSFORMS_MATHEMATICALSUPPORT_H
#define ZKC_TRANSFORMS_MATHEMATICALSUPPORT_H
#include "zkc/Dialect/Operations.h"
namespace zkc::mathematical {
// Helpers operate only on an owned candidate whose original module passed
// admission. Work budgets are shared across every selected definition.
mlir::LogicalResult inlineHelpers(mlir::Operation *body, unsigned &remaining,
                                  uint64_t &indices,
                                  mlir::SymbolTableCollection &symbols,
                                  mlir::Operation *lookupRoot = nullptr,
                                  uint64_t *work = nullptr);
// Charge every operation of one helper, including the helper itself, its
// terminator and operations no result reaches, to the budgets inlineHelpers
// charges its callees to: one operation, its operand/result slots, and one
// more than those slots of optional work. Callers charge a root helper before
// cloning it so the clone never exceeds what the budgets admit.
mlir::LogicalResult chargeHelperOperations(mlir::Operation *helper,
                                           unsigned &remaining,
                                           uint64_t &indices,
                                           uint64_t *work = nullptr);
// Closed execution vocabulary of the mathematical recipes. Admission of a
// data signature alone does not establish that an operation is total.
bool isCalculationContract(llvm::StringRef contract);
mlir::LogicalResult
verifyCalculationRecipes(protocol_ir::ProtocolModuleOp original,
                         protocol_ir::ProtocolModuleOp candidate,
                         llvm::ArrayRef<local::FuncOp> functions);
mlir::LogicalResult lowerCalculations(protocol_ir::ProtocolModuleOp unit,
                                      llvm::ArrayRef<local::FuncOp> functions);
// Internal rewrite entry used by preparation and participant simplification.
// The caller has already admitted the complete unit.
mlir::LogicalResult simplifyCalculations(mlir::Operation *body);
// Build retained obligations from the original common definition.
mlir::ArrayAttr statementBindings(protocol_ir::MathematicalOp program,
                                  mlir::SymbolTableCollection &symbols);
// Both complete modules have passed ordinary verification, including the
// module-owned calculation-attribution check.
mlir::LogicalResult verifyMathLowering(protocol_ir::ProtocolModuleOp original,
                                       protocol_ir::ProtocolModuleOp candidate);
} // namespace zkc::mathematical
namespace zkc::poly {
mlir::LogicalResult eliminatePolynomials(mlir::Block &body,
                                         uint64_t &remaining);
}
#endif
