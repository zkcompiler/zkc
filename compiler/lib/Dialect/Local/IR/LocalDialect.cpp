#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
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
