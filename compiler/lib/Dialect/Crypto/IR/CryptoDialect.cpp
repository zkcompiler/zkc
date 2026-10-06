#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Crypto/IR/CryptoOps.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/Crypto/IR/cryptoDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Crypto/IR/cryptoOps.cpp.inc"

void zkc::crypto::CryptoDialect::initialize() {
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Crypto/IR/cryptoOps.cpp.inc"
      >();
}
