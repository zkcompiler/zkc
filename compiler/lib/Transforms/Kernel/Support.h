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
// Return the actual complete, admitted executable candidate while preserving
// the original Kernel source. The caller owns independent source/candidate
// correspondence checking before publication.
mlir::OwningOpRef<mlir::ModuleOp>
proposeKernelLowering(mlir::ModuleOp source,
                      MathematicalSelectionPolicy policy = {},
                      mathematical::RealizationTrace *trace = nullptr);
// Checked Kernel-to-Kernel normalization; generated-operation identities refer
// to the returned owned unit and remain valid when that unit is adopted.
mlir::OwningOpRef<ModuleOp>
normalizeUnit(ModuleOp unit, uint64_t &remaining,
              llvm::DenseSet<mlir::Operation *> &polynomialGenerated);
mlir::FailureOr<MathematicalSelectionPolicy>
selectionPolicy(CallOp call, MathematicalSelectionPolicy fallback);

// Convert one immutable normalized Kernel entry into an owned executable
// candidate through a checked standard numerical schedule. Local is output.
// Callers share copy/site and realization budgets across the entire module.
// Copy/site quotas charge the selected attempt (or a terminal failure).
// A bulk attempt requires work's separate cumulative discarded-construction
// reserve to cover both incoming quotas; otherwise select ordered execution.
// At most one optional-comparison retry can debit that reserve, preserving the
// ordered construction quotas without refunding spent speculative work.
// Failure publishes nothing. Only optional comparison capacity permits retry.
mlir::OwningOpRef<mlir::ModuleOp>
realizeEntry(ModuleOp source, llvm::StringRef callSite,
             MathematicalSelectionPolicy policy,
             mathematical::RealizationWork &work, uint64_t &remaining,
             uint64_t &remainingBytes, finite::VerificationLimits limits = {},
             mathematical::RealizationTrace *trace = nullptr);

// Admit a closed Local fragment in the existing executable owner. It has no
// participant Entry, so whole-program admission applies after insertion into
// its caller; reuse the existing local-definition grammar and resource checks.
mlir::LogicalResult verifyRecipeOutput(mlir::ModuleOp candidate);

// Independent complete-candidate reader, including executable admission,
// output interface, binding use and occurrence roots. The typed result allows
// a producer to retry optional comparison exhaustion without diagnosing it.
mlir::LogicalResult
verifyEntryRecipes(ModuleOp source, mlir::ModuleOp candidate,
                   llvm::StringRef callSite,
                   MathematicalSelectionPolicy policy = {},
                   finite::VerificationLimits limits = {},
                   finite::VerificationResult *outcome = nullptr);

// Match the original Kernel function at an actual Local or scheduled cursor.
// Source and target symbol contexts are distinct; call-specific identity and
// policy are supplied explicitly and never stored in the mathematical source.
mlir::FailureOr<llvm::SmallVector<mlir::Value>> verifyKernelRecipes(
    mlir::func::FuncOp source, mlir::Operation *targetRoot,
    llvm::StringRef callSite, mlir::ValueRange arguments,
    mlir::Operation *&cursor, uint64_t &remaining, uint64_t &remainingBytes,
    MathematicalSelectionPolicy policy, finite::VerificationLimits limits,
    finite::VerificationResult &outcome);
} // namespace zkc::kernel
#endif
