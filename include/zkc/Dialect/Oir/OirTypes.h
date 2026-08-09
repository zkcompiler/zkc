//===- OirTypes.h - Operator-layer types ------------------------*- C++ -*-===//
#ifndef ZKC_DIALECT_OIR_OIRTYPES_H
#define ZKC_DIALECT_OIR_OIRTYPES_H

#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/Types.h"

namespace zkc {
namespace oir {

/// The closed provenance vocabulary (docs/spec/carrier.md §6.1): a
/// value's birthplace, carried in its type.
inline bool isKnownOrigin(llvm::StringRef origin) {
  return origin == "public" || origin == "pinned" || origin == "wire" ||
         origin == "sampled" || origin == "derived" || origin == "hole";
}

} // namespace oir
} // namespace zkc

#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Oir/OirOpsTypes.h.inc"

#endif // ZKC_DIALECT_OIR_OIRTYPES_H
