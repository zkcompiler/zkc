#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Entry/IR/EntryOps.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/Entry/IR/entryDialect.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Entry/IR/entryTypes.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Entry/IR/entryOps.cpp.inc"
void zkc::entry::EntryDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/Entry/IR/entryTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Entry/IR/entryOps.cpp.inc"
      >();
}
