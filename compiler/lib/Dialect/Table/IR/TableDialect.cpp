#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Table/IR/TableOps.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/Table/IR/tableDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Table/IR/tableOps.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Table/IR/tableTypes.cpp.inc"

void zkc::table::TableDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/Table/IR/tableTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Table/IR/tableOps.cpp.inc"
      >();
}
