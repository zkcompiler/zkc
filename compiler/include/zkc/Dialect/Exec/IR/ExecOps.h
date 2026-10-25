#ifndef ZKC_DIALECT_EXEC_IR_EXECOPS_H
#define ZKC_DIALECT_EXEC_IR_EXECOPS_H
#include "mlir/Bytecode/BytecodeOpInterface.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/IR/OpImplementation.h"
#include "mlir/Interfaces/ControlFlowInterfaces.h"
#include "mlir/Interfaces/InferTypeOpInterface.h"
#include "zkc/Dialect/Exec/IR/ExecDialect.h"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Exec/IR/execTypes.h.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Exec/IR/execOps.h.inc"
#endif
