#ifndef ZKC_TRANSFORMS_COMPUTATION_FRONTIERVERIFICATION_H
#define ZKC_TRANSFORMS_COMPUTATION_FRONTIERVERIFICATION_H

#include "zkc/Support/OptimizationOutcome.h"
#include "zkc/Transforms/Computation.h"
#include "llvm/ADT/SmallVector.h"
#include <cstdint>
#include <optional>

namespace zkc::computation {
// Non-owning evidence from independent normalization occurrence verification.
// All handles refer to the immutable normalized-before-frontier snapshot.
// Membership must never be inferred from missing site attributes or supplied
// by the frontier producer. All other entry operations are concrete
// occurrences.
struct FrontierNormalizationOrigin {
  mlir::func::FuncOp entry;
  llvm::SmallVector<mlir::Operation *> polynomialGenerated;
};

// Read the actual scoped proposal, preserving the entire ordered module
// context and original data-port prefixes. Scope and outcome coordinates stay
// separate: only selected compute success blocks and root return/failure
// packaging may grow their logical payload. Only checked generated operations
// may reuse actual earlier generated producers in the same participant block.
// Generated projections may forward exact retained pack coordinates through
// actual ports. Concrete producers remain fixed. Does not emit IR.
// Both readers debit the caller's cumulative transaction allowance. Capacity
// output is cleared on entry and set only for a failed checking debit or depth
// limit; depth limits have no requested/available work debit.
mlir::LogicalResult verifyComputationFrontier(
    mlir::ModuleOp normalizedBefore, mlir::ModuleOp actualAfter,
    llvm::ArrayRef<FrontierNormalizationOrigin> checkedOrigins,
    uint64_t &remaining, std::optional<CapacityCause> *capacity = nullptr);

// Explicit records for the preceding source -> normalized-context edge.
// Independently checked per-call mathematics/occurrences are a prerequisite;
// this record grants only the named callee rewrite and appended unit, never
// changes to source units, interfaces, attributes, actions, or ordered SSA.
struct ComputationNormalizationRewrite {
  mlir::Operation *sourceCall;
  mlir::Operation *normalizedCall;
  mlir::ModuleOp normalizedUnit;
};
mlir::LogicalResult verifyComputationNormalizationContext(
    mlir::ModuleOp source, mlir::ModuleOp normalized,
    llvm::ArrayRef<ComputationNormalizationRewrite> checkedRewrites,
    uint64_t &remaining, std::optional<CapacityCause> *capacity = nullptr);
} // namespace zkc::computation
#endif
