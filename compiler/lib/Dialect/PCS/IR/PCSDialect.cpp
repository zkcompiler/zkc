#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/IR.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/PCS/IR/pcsDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/PCS/IR/pcsOps.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/PCS/IR/pcsTypes.cpp.inc"
void zkc::PCSDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/PCS/IR/pcsTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/PCS/IR/pcsOps.cpp.inc"
      >();
}
