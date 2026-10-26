#ifndef ZKC_TRANSFORMS_KERNEL_SCHEDULE_H
#define ZKC_TRANSFORMS_KERNEL_SCHEDULE_H
#include "../FiniteVerification.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "zkc/Support/OptimizationOutcome.h"
#include "zkc/Transforms/Kernel.h"
#include <optional>
namespace zkc::kernel {
// Closed private packet: two zero-trip Local bound admissions, exact ui64/i64
// bridges, unit i64 step, unsigned scf.for, and exact induction bridge. The
// state prefix is observable; the invariant-result suffix must never escape.
struct ScheduledLoop {
  mlir::scf::ForOp loop;
  mlir::Value lower, upper;
  unsigned states;
  llvm::SmallVector<mlir::Value> arguments;
  llvm::SmallVector<mlir::Value> inputs;
};
// Pure schema inspection. A present result advances the cursor. An empty
// result means no packet matched; failure means inspection capacity ran out.
// Zero remaining work alone does not mean failure. Never emits IR.
mlir::FailureOr<std::optional<ScheduledLoop>>
readScheduledLoop(mlir::Operation *&cursor);
// Production readers share a cumulative required allowance, including nested
// frame scans. Exhaustion returns failure and sets the allowance to zero.
mlir::FailureOr<std::optional<ScheduledLoop>>
readScheduledLoop(mlir::Operation *&cursor, uint64_t &remaining);
llvm::SmallVector<mlir::Value> traversalArguments(mlir::Block *);
mlir::func::FuncOp readScheduledFunction(mlir::ModuleOp);
// Producer consumes an admitted Local recipe fragment, returning standard
// func.func plus scheduled control. Required copying is charged before work.
mlir::OwningOpRef<mlir::ModuleOp>
scheduleEntry(mlir::ModuleOp local, uint64_t &remaining,
              std::optional<CapacityCause> *capacity = nullptr);
// Real executable consumer: publishes scoped Func/CF execution from the actual
// schedule. It does not retain or regenerate the earlier recipe fragment.
mlir::OwningOpRef<mlir::ModuleOp>
consumeSchedule(mlir::ModuleOp schedule, uint64_t &remaining,
                std::optional<CapacityCause> *capacity = nullptr);
mlir::LogicalResult
verifyScheduleLowering(mlir::ModuleOp schedule, mlir::ModuleOp local,
                       uint64_t *shared = nullptr,
                       finite::VerificationResult *outcome = nullptr);
// Reads the original normalized Kernel directly against actual SCF operations
// through the finite reader's candidate-control adapter. No schedule producer
// or scheduled-to-Local conversion is invoked by this checker.
mlir::LogicalResult
verifyEntrySchedule(mlir::ModuleOp source, mlir::ModuleOp schedule,
                    llvm::StringRef callSite,
                    MathematicalSelectionPolicy policy = {},
                    finite::VerificationLimits limits = {},
                    finite::VerificationResult *outcome = nullptr);
} // namespace zkc::kernel
#endif
