#ifndef ZKC_DIALECT_RUNTIME_EXECUTION_H
#define ZKC_DIALECT_RUNTIME_EXECUTION_H

#include "mlir/Dialect/Func/IR/FuncOps.h"

namespace zkc::runtime {
/// Check acquired-scope and transfer consumption on every actual CFG edge.
/// Function scope arguments are borrowed. Joins must agree on live ownership;
/// returned ownership is transferred once and other owned values must be gone.
/// Calls use the same borrowed-scope contract; the enclosing admission must
/// check every potential callee rather than treating this as a closure check.
/// This bounded analysis does not establish payload-borrow lifetime, frame
/// nesting, source association, invocation identity or native correspondence.
/// Those remain obligations of the enclosing executable-profile reader.
mlir::LogicalResult verifyScopeOwnership(mlir::func::FuncOp function);
} // namespace zkc::runtime

#endif
