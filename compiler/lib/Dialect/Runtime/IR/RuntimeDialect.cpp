#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/Runtime/IR/runtimeDialect.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Runtime/IR/runtimeTypes.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Runtime/IR/runtimeOps.cpp.inc"
void zkc::runtime::RuntimeDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/Runtime/IR/runtimeTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Runtime/IR/runtimeOps.cpp.inc"
      >();
}
