#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/IR.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/planDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/planOps.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/planTypes.cpp.inc"

void zkc::PlanDialect::initialize() {
  addTypes<ScalarType, DataType>();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/planOps.cpp.inc"
      >();
}
