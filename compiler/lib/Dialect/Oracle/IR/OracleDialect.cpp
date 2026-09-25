#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/IR.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/Oracle/IR/oracleDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Oracle/IR/oracleOps.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Oracle/IR/oracleTypes.cpp.inc"
void zkc::OracleDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/Oracle/IR/oracleTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Oracle/IR/oracleOps.cpp.inc"
      >();
}
