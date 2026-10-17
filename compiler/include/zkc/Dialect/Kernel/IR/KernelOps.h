#ifndef ZKC_DIALECT_KERNEL_IR_KERNELOPS_H
#define ZKC_DIALECT_KERNEL_IR_KERNELOPS_H

#include "mlir/Bytecode/BytecodeOpInterface.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/IR/OpImplementation.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/Interfaces/CallInterfaces.h"
#include "zkc/Dialect/Kernel/IR/KernelDialect.h"

#define GET_OP_CLASSES
#include "zkc/Dialect/Kernel/IR/kernelOps.h.inc"

namespace zkc::kernel {
// Return null for a missing or ambiguous public entry. Full formation belongs
// to the region verifier, after MLIR has verified nested operation invariants.
mlir::func::FuncOp getEntry(ModuleOp unit);
// Resolve only the exact public entry of a sibling Kernel unit; reject flat,
// deeper, helper and foreign-owner references. Does not imply unit admission.
mlir::func::FuncOp resolve(CallOp call, mlir::SymbolTableCollection &symbols);
} // namespace zkc::kernel

#endif
