#ifndef ZKC_TRANSFORMS_KERNEL_SCHEDULE_H
#define ZKC_TRANSFORMS_KERNEL_SCHEDULE_H
#include "../FiniteVerification.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "zkc/Support/OptimizationOutcome.h"
#include "zkc/Transforms/Kernel.h"
#include <optional>
namespace zkc::kernel {
// Real executable consumer: publishes scoped Func/CF execution from the actual
// scoped schedule. It does not retain or regenerate a mathematical recipe.
mlir::OwningOpRef<mlir::ModuleOp>
consumeSchedule(mlir::ModuleOp schedule, uint64_t &remaining,
                std::optional<CapacityCause> *capacity = nullptr);
mlir::LogicalResult
verifyScheduleLowering(mlir::ModuleOp schedule, mlir::ModuleOp candidate,
                       uint64_t *shared = nullptr,
                       finite::VerificationResult *outcome = nullptr);
// Reads the original normalized Kernel directly against actual SCF operations
// through the actual scoped SSA association. This checker does not invoke the
// schedule producer or the scoped CFG consumer.
mlir::LogicalResult
verifyEntrySchedule(mlir::ModuleOp source, mlir::ModuleOp schedule,
                    llvm::StringRef callSite,
                    MathematicalSelectionPolicy policy = {},
                    finite::VerificationLimits limits = {},
                    finite::VerificationResult *outcome = nullptr);
} // namespace zkc::kernel
#endif
