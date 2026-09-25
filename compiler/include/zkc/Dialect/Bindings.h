#ifndef ZKC_DIALECT_BINDINGS_H
#define ZKC_DIALECT_BINDINGS_H

#include "mlir/IR/Types.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Source/Model.h"

namespace zkc::protocol {
/// Logical IR operation for an installed contract; empty when no mapping
/// exists.
llvm::StringRef boundOperationName(llvm::StringRef contract);
mlir::Type decodeBoundType(mlir::MLIRContext *, const BoundType &);
llvm::Expected<BoundType> encodeBoundType(mlir::Type, bool physical);
llvm::Expected<source::OperationBinding> readBinding(mlir::Operation *);
llvm::Expected<source::OperationBinding> operationBinding(mlir::Operation *);
mlir::LogicalResult verifyBoundOperation(mlir::Operation *, bool physical);
} // namespace zkc::protocol

#endif
