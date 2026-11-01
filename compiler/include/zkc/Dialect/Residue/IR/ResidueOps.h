#ifndef ZKC_DIALECT_RESIDUE_IR_RESIDUEOPS_H
#define ZKC_DIALECT_RESIDUE_IR_RESIDUEOPS_H
#include "mlir/Bytecode/BytecodeOpInterface.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/Interfaces/InferTypeOpInterface.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "zkc/Dialect/Residue/IR/ResidueAttrs.h"
#define GET_OP_CLASSES
#include "zkc/Dialect/Residue/IR/residueOps.h.inc"
#endif
