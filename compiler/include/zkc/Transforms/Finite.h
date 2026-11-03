#ifndef ZKC_TRANSFORMS_FINITE_H
#define ZKC_TRANSFORMS_FINITE_H
#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Transforms/MathematicalSelection.h"
#include "zkc/Transforms/MathematicalTrace.h"
#include "zkc/Transforms/MathematicalWork.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include <string>
namespace zkc::finite {
/// Where a finite reader hands a total helper to its helper reader. The finite
/// reader owns the occurrence sequence: `site` issues the expected occurrence
/// of each helper operation, in source order. `depth` counts the selected
/// regions that enclose the invocation; helper readers continue counting from
/// it, so one nesting bound covers arms and helper crossings.
struct HelperPosition {
  llvm::function_ref<mlir::FailureOr<std::string>()> site;
  unsigned depth = 0;
};
using HelperReader =
    llvm::function_ref<mlir::FailureOr<llvm::SmallVector<mlir::Value>>(
        mlir::Operation *, mlir::ValueRange, mlir::Operation *&,
        const HelperPosition &)>;
} // namespace zkc::finite
#endif
