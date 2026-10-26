#ifndef ZKC_TRANSFORMS_SCOPEDCALLBACK_H
#define ZKC_TRANSFORMS_SCOPEDCALLBACK_H

#include "mlir/IR/ValueRange.h"
#include "mlir/Support/LogicalResult.h"
#include "llvm/ADT/STLFunctionalExtras.h"

namespace mlir::func {
class FuncOp;
}
namespace zkc::exec {
class ScopedExecutionBuilder;
}
namespace zkc::finite {
// A reached callback can stop without producing its result. This is separate
// from construction failure and from a successful callback with no outputs.
// These data/signature declarations contain no recognition or recipe choice.
struct ScopedCallbackResult {
  llvm::SmallVector<mlir::Value> values;
  bool stopped = false;
};
using ScopedCallbackEmitter =
    llvm::function_ref<mlir::FailureOr<ScopedCallbackResult>(
        mlir::func::FuncOp, mlir::ValueRange, llvm::StringRef,
        exec::ScopedExecutionBuilder &)>;
using ScopedCallbackReader =
    llvm::function_ref<mlir::FailureOr<ScopedCallbackResult>(
        mlir::func::FuncOp, mlir::ValueRange, llvm::StringRef,
        mlir::Operation *&)>;
} // namespace zkc::finite
#endif
