#ifndef ZKC_DIALECT_LOCAL_IR_LOCALOPS_H
#define ZKC_DIALECT_LOCAL_IR_LOCALOPS_H
#include "mlir/Bytecode/BytecodeOpInterface.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/IR/OpImplementation.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/Interfaces/CallInterfaces.h"
#include "mlir/Interfaces/ControlFlowInterfaces.h"
#include "mlir/Interfaces/FunctionInterfaces.h"
#include "mlir/Interfaces/InferTypeOpInterface.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "zkc/Dialect/KernelSupport.h"
#include "zkc/Dialect/Local/IR/LocalTypes.h"
#include "zkc/Interfaces/LinearContraction.h"
#include "zkc/Interfaces/PreparationCallable.h"
#define GET_OP_CLASSES
#include "zkc/Dialect/Local/IR/localOps.h.inc"

#endif
