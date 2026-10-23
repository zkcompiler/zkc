#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/Local/IR/localDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Local/IR/localOps.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Local/IR/localTypes.cpp.inc"

void zkc::local::LocalDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/Local/IR/localTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Local/IR/localOps.cpp.inc"
      >();
}

LogicalResult zkc::local::BoolConstantOp::verify() {
  if (getOutput().getType().isSignlessInteger(1))
    return success();
  auto type = zkc::protocol::encodeBoundType(getOutput().getType(), true);
  if (!type) {
    llvm::consumeError(type.takeError());
    return zkc::diagnostics::emit(emitOpError(), "native-boolean-type");
  }
  if (type->spelling() != "bool@native.bool/0")
    return zkc::diagnostics::emit(emitOpError(), "native-boolean-type");
  return success();
}
