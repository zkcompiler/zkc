#include "envelope/Envelope.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Operations.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "envelope/EnvelopeDialect.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "envelope/EnvelopeTypes.cpp.inc"
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
#define GET_OP_CLASSES
#include "envelope/EnvelopeOps.cpp.inc"
#pragma GCC diagnostic pop
void envelope::EnvelopeDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "envelope/EnvelopeTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "envelope/EnvelopeOps.cpp.inc"
      >();
}
