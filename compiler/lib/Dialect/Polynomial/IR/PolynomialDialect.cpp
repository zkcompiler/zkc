#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/IR.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/Polynomial/IR/polyDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Polynomial/IR/polyOps.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Polynomial/IR/polyTypes.cpp.inc"

void zkc::PolynomialDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/Polynomial/IR/polyTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Polynomial/IR/polyOps.cpp.inc"
      >();
}
