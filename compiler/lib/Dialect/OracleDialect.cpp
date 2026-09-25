#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/IR.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/oracleDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/oracleOps.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/oracleTypes.cpp.inc"
void zkc::OracleDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/oracleTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/oracleOps.cpp.inc"
      >();
}
