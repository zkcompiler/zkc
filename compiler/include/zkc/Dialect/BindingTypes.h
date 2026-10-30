#ifndef ZKC_DIALECT_BINDING_TYPES_H
#define ZKC_DIALECT_BINDING_TYPES_H

#include "mlir/IR/Types.h"
#include "zkc/Contracts/Bindings.h"

namespace zkc::protocol {
/// Neutral input boundary. Strictly admit bytes before decoding, using only
/// already loaded native owners; never register or load a caller's dialects.
mlir::Type decodeBoundType(mlir::MLIRContext *, const BoundType &);
/// Canonical native-to-neutral type boundary. Check actual native formation,
/// unique catalog observation and byte-profile limits before publishing exact
/// ordered identity and complete physical children. Never print, parse or
/// reconstruct a native type to admit it. Failures emit no diagnostics.
llvm::Expected<BoundType> encodeBoundType(mlir::Type, bool physical);
} // namespace zkc::protocol

#endif
