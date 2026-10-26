#ifndef ZKC_TRANSFORMS_KERNEL_FRONTIERVERIFICATION_H
#define ZKC_TRANSFORMS_KERNEL_FRONTIERVERIFICATION_H

#include "zkc/Transforms/Kernel.h"
#include "llvm/ADT/SmallVector.h"
#include <cstdint>

namespace zkc::kernel {
// Non-owning evidence from independent normalization occurrence verification.
// All handles refer to the immutable normalized-before-frontier snapshot.
// Membership must never be inferred from missing site attributes or supplied
// by the frontier producer. All other entry operations are concrete
// occurrences.
struct FrontierNormalizationOrigin {
  mlir::func::FuncOp entry;
  llvm::SmallVector<mlir::Operation *> polynomialGenerated;
};

// Read the actual proposal, preserving the entire ordered module context and
// original port prefixes. Only checked generated operations may reuse actual
// earlier generated producers in the same participant block. Generated
// projections may forward exact retained pack coordinates through actual ports.
// Concrete producers remain fixed. Does not emit IR.
mlir::LogicalResult
verifyKernelFrontier(mlir::ModuleOp normalizedBefore,
                     mlir::ModuleOp actualAfter,
                     llvm::ArrayRef<FrontierNormalizationOrigin> checkedOrigins,
                     uint64_t &remaining);

// Explicit records for the preceding source -> normalized-context edge.
// Independently checked per-call mathematics/occurrences are a prerequisite;
// this record grants only the named callee rewrite and appended unit, never
// changes to source units, interfaces, attributes, actions, or ordered SSA.
struct KernelNormalizationRewrite {
  mlir::Operation *sourceCall;
  mlir::Operation *normalizedCall;
  mlir::ModuleOp normalizedUnit;
};
mlir::LogicalResult verifyKernelNormalizationContext(
    mlir::ModuleOp source, mlir::ModuleOp normalized,
    llvm::ArrayRef<KernelNormalizationRewrite> checkedRewrites,
    uint64_t &remaining);
} // namespace zkc::kernel
#endif
