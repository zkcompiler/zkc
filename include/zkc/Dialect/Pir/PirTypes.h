//===- PirTypes.h - Protocol IR types ---------------------------*- C++ -*-===//
#ifndef ZKC_DIALECT_PIR_PIRTYPES_H
#define ZKC_DIALECT_PIR_PIRTYPES_H

#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/Types.h"

namespace zkc {
namespace pir {

/// The thread/dep edge type: the builtin `token`. All C++ code obtains it
/// through this accessor, so moving to a dialect-local type — should the
/// builtin ever change upstream — is a one-line swap
/// (docs/spec/carrier.md §3).
inline mlir::Type getThreadType(mlir::MLIRContext *ctx) {
  return mlir::TokenType::get(ctx);
}

} // namespace pir
} // namespace zkc

#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Pir/PirOpsTypes.h.inc"

#endif // ZKC_DIALECT_PIR_PIRTYPES_H
