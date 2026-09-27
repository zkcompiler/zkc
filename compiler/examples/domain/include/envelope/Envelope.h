#ifndef EXAMPLE_ENVELOPE_H
#define EXAMPLE_ENVELOPE_H
#include "mlir/Bytecode/BytecodeOpInterface.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/Dialect.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "zkc/Dialect/Properties.h"
#include "zkc/Dialect/Types.h"

#include "envelope/EnvelopeDialect.h.inc"
#define GET_TYPEDEF_CLASSES
#include "envelope/EnvelopeTypes.h.inc"
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
#define GET_OP_CLASSES
#include "envelope/EnvelopeOps.h.inc"
#pragma GCC diagnostic pop
#endif
