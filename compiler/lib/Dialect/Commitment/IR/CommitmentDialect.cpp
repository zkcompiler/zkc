#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Commitment/IR/CommitmentOps.h"
#include "zkc/Dialect/TypeAdapters.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/Commitment/IR/commitmentDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Commitment/IR/commitmentOps.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Commitment/IR/commitmentTypes.cpp.inc"
void zkc::commitment::CommitmentDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/Commitment/IR/commitmentTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Commitment/IR/commitmentOps.cpp.inc"
      >();
  zkc::protocol::type_adapters::attachCatalogTypeModels(*this);
}
