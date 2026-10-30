#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Crypto/IR/CryptoOps.h"
#include "zkc/Dialect/Crypto/IR/CryptoTypes.h"
#include "zkc/Dialect/TypeAdapters.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/Crypto/IR/cryptoDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Crypto/IR/cryptoOps.cpp.inc"

#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Crypto/IR/cryptoTypes.cpp.inc"

void zkc::crypto::CryptoDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/Crypto/IR/cryptoTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Crypto/IR/cryptoOps.cpp.inc"
      >();
  zkc::protocol::type_adapters::attachCatalogTypeModels(*this);
}
