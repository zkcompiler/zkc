#ifndef ZKC_DIALECT_POLYNOMIAL_IR_POLYNOMIALOPS_H
#define ZKC_DIALECT_POLYNOMIAL_IR_POLYNOMIALOPS_H
#include "mlir/Bytecode/BytecodeOpInterface.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/IR/OpImplementation.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/Interfaces/ControlFlowInterfaces.h"
#include "mlir/Interfaces/InferTypeOpInterface.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/KernelSupport.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialTypes.h"
#include "zkc/Interfaces/LinearContraction.h"
#include "zkc/Interfaces/Mathematical.h"
#define GET_OP_CLASSES
#include "zkc/Dialect/Polynomial/IR/polyOps.h.inc"

#endif
