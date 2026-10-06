#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Plan/IR/PlanOps.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/Plan/IR/planDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Plan/IR/planOps.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Plan/IR/planTypes.cpp.inc"

void zkc::plan::PlanDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/Plan/IR/planTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Plan/IR/planOps.cpp.inc"
      >();
}

LogicalResult zkc::plan::BoolConstantOp::verify() {
  auto type = zkc::protocol::encodeBoundType(getOutput().getType(), true);
  if (!type) {
    llvm::consumeError(type.takeError());
    return zkc::diagnostics::emit(emitOpError(), "native-boolean-type");
  }
  if (type->spelling() != "bool@native.bool/1")
    return zkc::diagnostics::emit(emitOpError(), "native-boolean-type");
  return success();
}
