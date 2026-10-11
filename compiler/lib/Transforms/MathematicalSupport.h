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
// Bounded derived view: every map formula is admitted, including dead work;
// entries identify exactly a multiplication of two rowwise argument slots in
// scalar operand order. Reduction recipe selection remains separate; no IR or
// expression graph is stored in this view.
mlir::FailureOr<std::map<std::string, std::pair<unsigned, unsigned>>>
describeMapProducts(mlir::ModuleOp module);
// Private reduction-inventory override. Map admission and installed lane
// recipes are unchanged; the independent reader receives neither inventory.
struct ReductionRecipe;
mlir::LogicalResult
fuseVectorReductions(mlir::ModuleOp module,
                     protocol::AlgorithmExpansionState &state,
                     llvm::ArrayRef<ReductionRecipe> reductions);
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
// The typed outcome allows the private producer to retry only optional finite
// comparison exhaustion; it does not weaken the actual recipe reader.
mlir::LogicalResult
verifyCalculationRecipes(protocol_ir::ProtocolModuleOp original,
                         protocol_ir::ProtocolModuleOp candidate,
                         llvm::ArrayRef<local::FuncOp> functions,
                         finite::VerificationLimits limits,
                         finite::VerificationResult &outcome);
class CheckedHelperNormalizations;
// Compare original local.realize helpers to complete actual executable bodies,
// composing independently checked normalization proposals and recipe reading.
mlir::LogicalResult
verifyRealizedHelperRecipes(protocol_ir::ProtocolModuleOp original,
                            protocol_ir::ProtocolModuleOp candidate,
                            llvm::ArrayRef<local::FuncOp> functions);
// Reuse a proposal scope already checked against this exact original unit.
mlir::LogicalResult
verifyRealizedHelperRecipes(protocol_ir::ProtocolModuleOp original,
                            protocol_ir::ProtocolModuleOp candidate,
                            llvm::ArrayRef<local::FuncOp> functions,
                            const CheckedHelperNormalizations &helpers);
// Success preserves function handles and replaces their checked bodies, adding
// only generated bindings. Failure leaves the unit unchanged; outer services
// own complete module admission.
mlir::LogicalResult lowerCalculations(protocol_ir::ProtocolModuleOp unit,
                                      llvm::ArrayRef<local::FuncOp> functions,
                                      MathematicalSelectionPolicy policy = {},
                                      RealizationWork *work = nullptr);
mlir::LogicalResult expandMathRealizations(mlir::ModuleOp module,
                                           MathematicalSelectionPolicy policy,
                                           RealizationWork *work,
                                           finite::VerificationLimits limits);
// Capacity-configured private entry; uses the same checked candidate path.
mlir::LogicalResult lowerCalculations(protocol_ir::ProtocolModuleOp unit,
                                      llvm::ArrayRef<local::FuncOp> functions,
                                      MathematicalSelectionPolicy policy,
                                      RealizationWork *work,
                                      finite::VerificationLimits limits);
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
