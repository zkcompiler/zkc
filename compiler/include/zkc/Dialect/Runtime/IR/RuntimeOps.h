#ifndef ZKC_DIALECT_RUNTIME_IR_RUNTIMEOPS_H
#define ZKC_DIALECT_RUNTIME_IR_RUNTIMEOPS_H
#include "mlir/Bytecode/BytecodeOpInterface.h"
#include "mlir/IR/OpDefinition.h"
#include "zkc/Dialect/BoundOperations.h"
#include "zkc/Dialect/Runtime/IR/RuntimeTypes.h"
#define GET_OP_CLASSES
#include "zkc/Dialect/Runtime/IR/runtimeOps.h.inc"
#endif
