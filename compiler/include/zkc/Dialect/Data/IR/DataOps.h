#ifndef ZKC_DIALECT_DATA_IR_DATAOPS_H
#define ZKC_DIALECT_DATA_IR_DATAOPS_H
#include "mlir/Bytecode/BytecodeOpInterface.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/IR/OpImplementation.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/Interfaces/ControlFlowInterfaces.h"
#include "mlir/Interfaces/InferTypeOpInterface.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/BoundOperations.h"
#include "zkc/Dialect/Data/IR/DataDialect.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Interfaces/Mathematical.h"
#define GET_OP_CLASSES
#include "zkc/Dialect/Data/IR/dataOps.h.inc"
#endif
