//===- OirTypes.cpp - Operator-layer types ----------------------*- C++ -*-===//
#include "zkc/Dialect/Oir/OirTypes.h"

#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Oir/OirDialect.h"
#include "llvm/ADT/TypeSwitch.h"

#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Oir/OirOpsTypes.cpp.inc"

using namespace mlir;

LogicalResult
zkc::oir::ValType::verify(llvm::function_ref<InFlightDiagnostic()> emitError,
                          StringRef valueClass, StringRef origin) {
  (void)valueClass;
  if (!zkc::oir::isKnownOrigin(origin))
    return emitError() << "unknown provenance '" << origin
                       << "' (expected public, pinned, wire, sampled, "
                          "derived, or hole)";
  return success();
}

void zkc::oir::OirDialect::registerTypes() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/Oir/OirOpsTypes.cpp.inc"
      >();
}
