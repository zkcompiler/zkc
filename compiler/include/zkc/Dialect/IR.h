#ifndef ZKC_DIALECT_IR_H
#define ZKC_DIALECT_IR_H
#include "mlir/Bytecode/BytecodeOpInterface.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/Dialect.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/IR/OpImplementation.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/Interfaces/ControlFlowInterfaces.h"
#include "mlir/Interfaces/InferTypeOpInterface.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "zkc/Dialect/Properties.h"
#include "llvm/Support/JSON.h"

#include "zkc/Dialect/algebraDialect.h.inc"
#include "zkc/Dialect/claimDialect.h.inc"
#include "zkc/Dialect/oracleDialect.h.inc"
#include "zkc/Dialect/pcsDialect.h.inc"
#include "zkc/Dialect/pirDialect.h.inc"
#include "zkc/Dialect/planDialect.h.inc"
#include "zkc/Dialect/polyDialect.h.inc"
#include "zkc/Dialect/relationDialect.h.inc"
#include "zkc/Interfaces/LinearContraction.h"
#include "zkc/Interfaces/SourceOpInterface.h.inc"

#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/pirTypes.h.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/algebraTypes.h.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/polyTypes.h.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/planTypes.h.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/pcsTypes.h.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/oracleTypes.h.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/claimTypes.h.inc"
// Cross-dialect parent traits require the shared forward declarations.
#define GET_OP_CLASSES
#include "zkc/Dialect/Operations.h.inc"
namespace zkc {
/// Register the built-in carriers without installing a source library model.
void registerDialects(mlir::DialectRegistry &registry);
mlir::LogicalResult verifyProgram(mlir::Operation *program);
} // namespace zkc
#endif
