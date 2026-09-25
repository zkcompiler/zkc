#include "mlir/IR/Builders.h"
#include "zkc/Dialect/IR.h"
using namespace mlir;

#include "zkc/Dialect/relationDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/relationOps.cpp.inc"

void zkc::RelationDialect::initialize() {
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/relationOps.cpp.inc"
      >();
}
