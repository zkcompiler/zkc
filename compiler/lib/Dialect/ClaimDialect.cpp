#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/IR.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/claimDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/claimOps.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/claimTypes.cpp.inc"
void zkc::ClaimDialect::initialize() {
  addTypes<ClaimPendingType, ClaimEvidenceType>();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/claimOps.cpp.inc"
      >();
}
