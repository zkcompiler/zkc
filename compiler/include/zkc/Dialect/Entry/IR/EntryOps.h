#ifndef ZKC_DIALECT_ENTRY_IR_ENTRYOPS_H
#define ZKC_DIALECT_ENTRY_IR_ENTRYOPS_H
#include "mlir/Bytecode/BytecodeOpInterface.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/IR/OpImplementation.h"
#include "zkc/Dialect/Entry/IR/EntryDialect.h"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Entry/IR/entryTypes.h.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Entry/IR/entryOps.h.inc"
#endif
