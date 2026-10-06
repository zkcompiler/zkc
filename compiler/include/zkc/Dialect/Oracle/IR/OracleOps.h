#ifndef ZKC_DIALECT_ORACLE_IR_ORACLEOPS_H
#define ZKC_DIALECT_ORACLE_IR_ORACLEOPS_H
#include "mlir/Bytecode/BytecodeOpInterface.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/IR/OpImplementation.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/Interfaces/ControlFlowInterfaces.h"
#include "mlir/Interfaces/InferTypeOpInterface.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "zkc/Dialect/KernelSupport.h"
#include "zkc/Dialect/Oracle/IR/OracleTypes.h"
#include "zkc/Interfaces/LinearContraction.h"
#define GET_OP_CLASSES
#include "zkc/Dialect/Oracle/IR/oracleOps.h.inc"

#endif
