#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/Protocol/IR/protocolDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Protocol/IR/protocolOps.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Protocol/IR/protocolTypes.cpp.inc"

void zkc::protocol_ir::ProtocolDialect::initialize() {
  initializeAttributes();
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/Protocol/IR/protocolTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Protocol/IR/protocolOps.cpp.inc"
      >();
}
