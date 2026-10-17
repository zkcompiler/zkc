#ifndef ZKC_TRANSFORMS_KERNEL_SUPPORT_H
#define ZKC_TRANSFORMS_KERNEL_SUPPORT_H
#include "../MathematicalSupport.h"
#include "zkc/Transforms/Kernel.h"

namespace zkc::kernel {
// Charge operations and SSA slots before copying a transient closure/body.
bool chargeCopy(mlir::Operation *, uint64_t &remaining);
// Producer shared by preparation and participant demand formation. Source is
// an admitted immutable closure; the wrapper is a private proposal containing
// total mathematics and at most one trailing partial guard.
mlir::LogicalResult formCalculation(local::FuncOp wrapper,
                                    mlir::Operation *sourceOwner,
                                    MathematicalSelectionPolicy policy);
// Independent exact comparison of original dependency bodies and domains.
mlir::LogicalResult verifyDependencies(mlir::Operation *sourceOwner,
                                       ModuleOp candidate);
// Independent exact standard-function substitution, including dead work and
// every actual argument/result coordinate. No mathematical optimization.
mlir::OwningOpRef<mlir::func::FuncOp> exactReadback(mlir::func::FuncOp source,
                                                    mlir::Operation *owner,
                                                    uint64_t &remaining);
// Temporary normalized mathematical subject, including checked extra concrete
// ports on uniquely invoked generated calculation wrappers. No recipe emission.
mlir::OwningOpRef<mlir::ModuleOp> prepareKernelLowering(mlir::ModuleOp source);
// Explicit checked normalization proposals. Source roots remain immutable;
// independent helper/polynomial meaning is checked before recipe consumption.
mlir::OwningOpRef<protocol_ir::ProtocolModuleOp>
normalizationWorkspace(ModuleOp unit, local::FuncOp &entry, uint64_t &remaining,
                       llvm::DenseSet<mlir::Operation *> &shareable);
// Exact context adapter for the already checked normalized mathematical body.
// No helper/polynomial normalizer or executable recipe emitter runs here.
mlir::OwningOpRef<protocol_ir::ProtocolModuleOp>
recipeWorkspace(ModuleOp unit, local::FuncOp &entry, llvm::StringRef callSite,
                uint64_t &remaining, uint64_t &remainingBytes);
mlir::FailureOr<MathematicalSelectionPolicy>
selectionPolicy(CallOp call, MathematicalSelectionPolicy fallback);
} // namespace zkc::kernel

namespace zkc::mathematical {
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
// Success preserves function handles and replaces their checked bodies, adding
// only generated bindings. Failure leaves the unit unchanged; outer services
// own complete module admission.
mlir::LogicalResult lowerCalculations(protocol_ir::ProtocolModuleOp unit,
                                      llvm::ArrayRef<local::FuncOp> functions,
                                      MathematicalSelectionPolicy policy = {},
                                      RealizationWork *work = nullptr,
                                      RealizationTrace *trace = nullptr);
// Capacity-configured private entry; uses the same checked candidate path.
mlir::LogicalResult lowerCalculations(protocol_ir::ProtocolModuleOp unit,
                                      llvm::ArrayRef<local::FuncOp> functions,
                                      MathematicalSelectionPolicy policy,
                                      RealizationWork *work,
                                      finite::VerificationLimits limits,
                                      RealizationTrace *trace = nullptr);

// Match an exact retained mathematical Local body at an arbitrary actual
// target cursor. Returns all outputs and advances past its recipes.
mlir::FailureOr<llvm::SmallVector<mlir::Value>>
verifyKernelRecipes(protocol_ir::ProtocolModuleOp source, local::FuncOp entry,
                    protocol_ir::ProtocolModuleOp candidate,
                    mlir::ValueRange arguments, mlir::Operation *&cursor,
                    uint64_t &remaining, MathematicalSelectionPolicy policy);
} // namespace zkc::mathematical
#endif
