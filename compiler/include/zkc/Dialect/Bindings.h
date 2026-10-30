#ifndef ZKC_DIALECT_BINDINGS_H
#define ZKC_DIALECT_BINDINGS_H

#include "mlir/IR/Types.h"
#include "zkc/Contracts/Binding.h"
#include "zkc/Contracts/Bindings.h"

namespace zkc::protocol {
/// Decode in already loaded dialects; return a null type if one is missing.
/// This operation never registers or loads dialects into the caller context.
mlir::Type decodeBoundType(mlir::MLIRContext *, const BoundType &);
llvm::Expected<BoundType> encodeBoundType(mlir::Type, bool physical);
/// Read a closed declaration. A Protocol module fixes its stage; a builtin
/// module admits logical or physical formation. Consumers of the latter must
/// also check their selected stage and actual invocation ports.
llvm::Expected<protocol::OperationBinding> readBinding(mlir::Operation *);
llvm::Expected<protocol::OperationBinding> operationBinding(mlir::Operation *);
} // namespace zkc::protocol

#endif
