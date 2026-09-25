#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/IR.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/algebraDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/algebraOps.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/algebraTypes.cpp.inc"

void zkc::AlgebraDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/algebraTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/algebraOps.cpp.inc"
      >();
}
