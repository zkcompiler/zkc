#ifndef ZKC_DIALECT_SELECTED_CONTROL_H
#define ZKC_DIALECT_SELECTED_CONTROL_H

#include "mlir/IR/Operation.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/Error.h"

namespace zkc {
/// Structural access to the registered closed selected-region vocabulary.
/// Callers supply formation before borrowing these associations. This view
/// establishes neither common control, reachability, nor resource succession.
bool isSelectedControl(mlir::Operation *);
llvm::Expected<llvm::SmallVector<mlir::Type>>
selectedPayloadTypes(mlir::Operation *, unsigned arm);
/// Forward a capture argument to its actual outer SSA operand. Payloads have
/// no outer operand of their type and return a null value.
mlir::Value selectedCapture(mlir::BlockArgument);
mlir::LogicalResult verifySelectedControl(mlir::Operation *);
/// Refuse a transformation whose installed profile requires unconditional
/// Protocol regions. Checks actual bodies, including dormant declarations,
/// before any candidate mutation. Existing scoped Exec control is unaffected.
llvm::Error requireUnconditionalProtocolControl(mlir::Operation *,
                                                llvm::StringRef diagnostic);
} // namespace zkc
#endif
