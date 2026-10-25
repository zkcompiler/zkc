#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/Local/IR/localDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Local/IR/localOps.cpp.inc"

void zkc::local::LocalDialect::initialize() {
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Local/IR/localOps.cpp.inc"
      >();
}
