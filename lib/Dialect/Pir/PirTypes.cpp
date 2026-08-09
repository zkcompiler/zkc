//===- PirTypes.cpp - Protocol IR types -------------------------*- C++ -*-===//
#include "zkc/Dialect/Pir/PirTypes.h"

#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Pir/PirDialect.h"
#include "llvm/ADT/TypeSwitch.h"

#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Pir/PirOpsTypes.cpp.inc"

void zkc::pir::PirDialect::registerTypes() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/Pir/PirOpsTypes.cpp.inc"
      >();
}
