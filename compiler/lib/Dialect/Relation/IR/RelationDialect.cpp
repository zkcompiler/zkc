#include "mlir/IR/Builders.h"
#include "zkc/Dialect/Relation/IR/RelationOps.h"
using namespace mlir;

#include "zkc/Dialect/Relation/IR/relationDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Relation/IR/relationOps.cpp.inc"

void zkc::relation::RelationDialect::initialize() {
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Relation/IR/relationOps.cpp.inc"
      >();
}
