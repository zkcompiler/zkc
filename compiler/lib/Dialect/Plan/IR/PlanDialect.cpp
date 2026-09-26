#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/IR.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/Plan/IR/planDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Plan/IR/planOps.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Plan/IR/planTypes.cpp.inc"

void zkc::PlanDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/Plan/IR/planTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Plan/IR/planOps.cpp.inc"
      >();
}
