#ifndef ZKC_DIALECT_BINDINGS_H
#define ZKC_DIALECT_BINDINGS_H

#include "mlir/IR/Types.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Source/Model.h"

namespace zkc::protocol {
/// Logical IR operation for an installed contract; empty when no mapping
/// exists.
llvm::StringRef boundOperationName(llvm::StringRef contract);
/// Whether an operation's ODS association supports this installed contract.
/// This is many-to-one: transcript observations share an operation. Unknown
/// operation names and uninstalled contracts return false. This query does not
/// validate a binding's arguments, types, parameters, or semantic properties.
bool operationSupportsContract(llvm::StringRef operationName,
                               llvm::StringRef contract);
/// Decode in already loaded dialects; return a null type if one is missing.
/// This operation never registers or loads dialects into the caller context.
mlir::Type decodeBoundType(mlir::MLIRContext *, const BoundType &);
llvm::Expected<BoundType> encodeBoundType(mlir::Type, bool physical);
llvm::Expected<source::OperationBinding> readBinding(mlir::Operation *);
llvm::Expected<source::OperationBinding> operationBinding(mlir::Operation *);
mlir::LogicalResult verifyBoundOperation(mlir::Operation *, bool physical);
} // namespace zkc::protocol

#endif
