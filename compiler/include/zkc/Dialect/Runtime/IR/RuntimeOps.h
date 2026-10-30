#ifndef ZKC_DIALECT_RUNTIME_IR_RUNTIMEOPS_H
#define ZKC_DIALECT_RUNTIME_IR_RUNTIMEOPS_H
#include "mlir/Bytecode/BytecodeOpInterface.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/Interfaces/CallInterfaces.h"
#include "zkc/Dialect/Exec/IR/ExecTypes.h"
#include "zkc/Dialect/Runtime/IR/RuntimeTypes.h"
#define GET_OP_CLASSES
#include "zkc/Dialect/Runtime/IR/runtimeOps.h.inc"
#endif
