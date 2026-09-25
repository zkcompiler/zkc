#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/IR.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/PIR/IR/pirDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/PIR/IR/pirOps.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/PIR/IR/pirTypes.cpp.inc"

void zkc::PIRDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/PIR/IR/pirTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/PIR/IR/pirOps.cpp.inc"
      >();
}
