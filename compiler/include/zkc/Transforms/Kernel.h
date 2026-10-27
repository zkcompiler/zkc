#ifndef ZKC_TRANSFORMS_KERNEL_H
#define ZKC_TRANSFORMS_KERNEL_H

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Transforms/MathematicalSelection.h"

namespace zkc::mathematical {
struct RealizationTrace;
}
namespace zkc::kernel {
/// Materialize logical invocations into scoped Func/CF execution,
/// retaining each call's policy. Numerical alternatives belong to
/// individual source occurrences; the reader checks their actual payloads.
/// Transactional Exec -> Exec edge, independently checked before publication;
/// no runtime frame, opcode or hidden target fallback.
mlir::LogicalResult lowerKernels(mlir::ModuleOp,
                                 MathematicalSelectionPolicy = {},
                                 mathematical::RealizationTrace * = nullptr);
/// Read original numerical closures and actual scoped candidate instructions.
/// Both complete subjects are admitted, including dormant numerical units.
mlir::LogicalResult verifyKernelLowering(mlir::ModuleOp original,
                                         mlir::ModuleOp candidate,
                                         MathematicalSelectionPolicy = {});
/// Exact closure comparison, including positional SSA, symbol references,
/// preconditions, nominal domains and unused operations. The entry name and
/// visibility may change; dependency names and domain identities may not.
mlir::LogicalResult verifyKernelClosure(mlir::Operation *sourceOwner,
                                        mlir::func::FuncOp sourceEntry,
                                        mlir::ModuleOp candidate);
} // namespace zkc::kernel
#endif
