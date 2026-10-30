#ifndef ZKC_DIALECT_RUNTIME_IR_RUNTIMETYPES_H
#define ZKC_DIALECT_RUNTIME_IR_RUNTIMETYPES_H
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/OpImplementation.h"
#include "zkc/Dialect/Runtime/IR/RuntimeDialect.h"
#include "zkc/Dialect/Runtime/IR/runtimeEnums.h.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Runtime/IR/runtimeTypes.h.inc"
#endif
