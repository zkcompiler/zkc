#ifndef ZKC_DIALECT_RELATION_IR_RELATIONOPS_H
#define ZKC_DIALECT_RELATION_IR_RELATIONOPS_H
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
#include "zkc/Dialect/Relation/IR/RelationDialect.h"
#include "zkc/Interfaces/LinearContraction.h"
#define GET_OP_CLASSES
#include "zkc/Dialect/Relation/IR/relationOps.h.inc"

#endif
