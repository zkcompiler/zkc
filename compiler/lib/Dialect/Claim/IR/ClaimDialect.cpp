#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/IR.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/Claim/IR/claimDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Claim/IR/claimOps.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Claim/IR/claimTypes.cpp.inc"
void zkc::ClaimDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/Claim/IR/claimTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Claim/IR/claimOps.cpp.inc"
      >();
}
