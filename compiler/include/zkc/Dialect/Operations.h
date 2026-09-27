#ifndef ZKC_DIALECT_OPERATIONS_H
#define ZKC_DIALECT_OPERATIONS_H
#include "mlir/Bytecode/BytecodeOpInterface.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/Dialect.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/IR/OpImplementation.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/Interfaces/ControlFlowInterfaces.h"
#include "mlir/Interfaces/InferTypeOpInterface.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "zkc/Dialect/Types.h"
#include "llvm/Support/JSON.h"

#include "zkc/Interfaces/LinearContraction.h"
#include "zkc/Interfaces/SourceOpInterface.h.inc"
namespace zkc::detail {
// Shared logical kernel policy used by ODS-generated standard verifiers.
::llvm::LogicalResult verifyLogicalKernel(::mlir::Operation *operation);
} // namespace zkc::detail

// Cross-dialect parent traits require the shared forward declarations.
#define GET_OP_CLASSES
#include "zkc/Dialect/Operations.h.inc"
#endif
