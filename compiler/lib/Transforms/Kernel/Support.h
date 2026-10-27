#ifndef ZKC_TRANSFORMS_KERNEL_SUPPORT_H
#define ZKC_TRANSFORMS_KERNEL_SUPPORT_H
#include "../MathematicalSupport.h"
#include "../NumericalSelection.h"
#include "zkc/Transforms/Kernel.h"

namespace zkc::kernel {
// Private demand-formation input. The condition belongs to the total wrapper;
// rejection remains an ordered Protocol action until scoped formation.
struct CalculationGuard {
  mlir::Value condition;
  mlir::StringAttr site;
};
mlir::LogicalResult
formCalculation(mlir::func::FuncOp wrapper, mlir::Operation *sourceOwner,
                MathematicalSelectionPolicy policy,
                std::optional<CalculationGuard> guard = std::nullopt);
// Charge operations and SSA slots before copying a transient closure/body.
bool chargeCopy(mlir::Operation *, uint64_t &remaining,
                std::optional<CapacityCause> *capacity = nullptr);
// Independent exact comparison of original dependency bodies and domains.
mlir::LogicalResult verifyDependencies(mlir::Operation *sourceOwner,
                                       mlir::ModuleOp candidate);
// Independent exact standard-function substitution, including dead work and
// every actual argument/result coordinate. No mathematical optimization.
mlir::OwningOpRef<mlir::func::FuncOp> exactReadback(mlir::func::FuncOp source,
                                                    mlir::Operation *owner,
                                                    uint64_t &remaining);
// Copy the actual selected helper and its closed mathematical dependencies,
// retaining all static premises. The source owner has already been admitted.
mlir::OwningOpRef<mlir::ModuleOp> closeComputation(mlir::func::FuncOp source,
                                                   uint64_t &remaining);
mlir::func::FuncOp resolveInvocation(mlir::Operation *call,
                                     mlir::SymbolTableCollection &symbols);
// Temporary normalized mathematical subject, including checked extra concrete
// ports on uniquely invoked generated calculation wrappers. No recipe emission.
// Executable binding choices are unchanged and do not affect normalization;
// callers can apply fixed requests to the owned result before recipe discovery.
// A frontier snapshot is needed only when checked polynomial origins permit
// port rewrites. Every performed copy and context check shares the given bound.
mlir::OwningOpRef<mlir::ModuleOp>
prepareKernelLowering(mlir::ModuleOp source, uint64_t *shared = nullptr,
                      std::optional<CapacityCause> *capacity = nullptr,
                      mathematical::NumericalSelection *selection = nullptr);
// Materialize only Kernel occurrences in an already private candidate. The
// containing numerical transaction owns cloning, map consumption and readback.
// An outcome sink delegates retry to that transaction. optionalConstruction
// classifies only its bounded copy/site envelope; it grants no replacement.
mlir::LogicalResult
materializeKernelCalls(mlir::ModuleOp candidate, MathematicalSelectionPolicy,
                       mathematical::RealizationTrace *,
                       mathematical::NumericalSelection &,
                       mathematical::VerificationDecision *outcome = nullptr,
                       bool optionalConstruction = false);

mlir::LogicalResult discoverKernelCalls(mlir::ModuleOp,
                                        MathematicalSelectionPolicy,
                                        mathematical::NumericalSelection &);
// Return the actual complete, admitted executable candidate while preserving
// the original Kernel source. The caller owns independent source/candidate
// correspondence checking before publication.
mlir::OwningOpRef<mlir::ModuleOp>
proposeKernelLowering(mlir::ModuleOp source,
                      MathematicalSelectionPolicy policy = {},
                      mathematical::RealizationTrace *trace = nullptr,
                      mathematical::NumericalSelection *selection = nullptr,
                      mlir::ModuleOp prepared = {});
// Checked Kernel-to-Kernel normalization; generated-operation identities refer
// to the returned owned unit and remain valid when that unit is adopted.
mlir::OwningOpRef<mlir::ModuleOp>
normalizeUnit(mlir::ModuleOp unit, uint64_t &remaining,
              llvm::DenseSet<mlir::Operation *> &polynomialGenerated,
              std::optional<CapacityCause> *capacity = nullptr);
mlir::FailureOr<MathematicalSelectionPolicy>
selectionPolicy(mlir::Operation *call, MathematicalSelectionPolicy fallback);
// The persisted call policy carries the three admitted family flags. Preserve
// the caller's remaining representation/construction policy when reading it.
inline mlir::FailureOr<MathematicalSelectionPolicy>
effectiveSelectionPolicy(mlir::Operation *call,
                         MathematicalSelectionPolicy fallback) {
  auto policy = selectionPolicy(call, fallback);
  if (succeeded(policy)) {
    policy->calculationBatching = fallback.calculationBatching;
    policy->numericalExpressions = fallback.numericalExpressions;
  }
  return policy;
}

// Convert one immutable normalized Kernel entry into an owned executable
// candidate through a checked standard numerical schedule. The output uses
// scoped Func/CF and Exec. selectedSchedule optionally receives the actual
// independently checked selected schedule, without replay or another copy.
// Callers share copy/site and realization budgets across the entire module.
// Copy/site quotas charge the selected attempt (or a terminal failure).
// Speculative construction is capped by the cumulative discard reserve before
// allocating. Optional comparison exhaustion advances only the reported source
// occurrence, preserving ordered construction quotas and all other choices.
// Required work and malformed/correspondence failures remain terminal.
mlir::OwningOpRef<mlir::ModuleOp>
realizeEntry(mlir::ModuleOp source, llvm::StringRef callSite,
             MathematicalSelectionPolicy policy,
             mathematical::RealizationWork &work, uint64_t &remaining,
             uint64_t &remainingBytes, finite::VerificationLimits limits = {},
             mathematical::RealizationTrace *trace = nullptr,
             mathematical::NumericalSelection *selection = nullptr,
             mathematical::VerificationDecision *outcome = nullptr,
             bool optionalConstruction = false,
             mlir::OwningOpRef<mlir::ModuleOp> *selectedSchedule = nullptr);

// Admit a closed scoped numerical fragment in the executable owner. It has no
// participant Entry; whole-program admission applies after insertion. Read the
// actual CFG, outlined bodies, resource origins and resolved binding closure.
mlir::LogicalResult verifyRecipeOutput(mlir::ModuleOp candidate);

// Independent comparison of the actual scoped source and numerical candidate.
mlir::LogicalResult verifyScopedNumericalContext(
    protocol_ir::ProtocolModuleOp original,
    protocol_ir::ProtocolModuleOp candidate,
    protocol_ir::ProtocolModuleOp declarations, MathematicalSelectionPolicy,
    mathematical::RealizationWork &, mathematical::VerificationDecision &);

// Independent complete-candidate reader, including executable admission,
// output interface, binding use and occurrence roots. The typed result allows
// a producer to retry optional comparison exhaustion without diagnosing it.
mlir::LogicalResult
verifyEntryRecipes(mlir::ModuleOp source, mlir::ModuleOp candidate,
                   llvm::StringRef callSite,
                   MathematicalSelectionPolicy policy = {},
                   finite::VerificationLimits limits = {},
                   finite::VerificationResult *outcome = nullptr,
                   mathematical::NumericalSelection *selection = nullptr);

// Match the original Kernel function at an actual Local or scheduled cursor.
// Source and target symbol contexts are distinct; call-specific identity and
// policy are supplied explicitly and never stored in the mathematical source.
mlir::FailureOr<llvm::SmallVector<mlir::Value>> verifyKernelRecipes(
    mlir::func::FuncOp source, mlir::Operation *targetRoot,
    llvm::StringRef callSite, mlir::ValueRange arguments,
    mlir::Operation *&cursor, uint64_t &remaining, uint64_t &remainingBytes,
    MathematicalSelectionPolicy policy, finite::VerificationLimits limits,
    finite::VerificationResult &outcome,
    mathematical::NumericalSelection *selection = nullptr);
} // namespace zkc::kernel
#endif
