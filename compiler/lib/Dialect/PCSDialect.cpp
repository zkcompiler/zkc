#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/IR.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/pcsDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/pcsOps.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/pcsTypes.cpp.inc"
void zkc::PCSDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/pcsTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/pcsOps.cpp.inc"
      >();
}
