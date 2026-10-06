#ifndef ZKC_DIALECT_CRYPTO_IR_CRYPTOOPS_H
#define ZKC_DIALECT_CRYPTO_IR_CRYPTOOPS_H
#include "mlir/Bytecode/BytecodeOpInterface.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/IR/OpImplementation.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/Interfaces/ControlFlowInterfaces.h"
#include "mlir/Interfaces/InferTypeOpInterface.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "zkc/Dialect/Crypto/IR/CryptoDialect.h"
#include "zkc/Dialect/KernelSupport.h"
#include "zkc/Interfaces/LinearContraction.h"
#define GET_OP_CLASSES
#include "zkc/Dialect/Crypto/IR/cryptoOps.h.inc"

#endif
