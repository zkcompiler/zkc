#ifndef ZKC_INTERFACES_COLLECTION_H
#define ZKC_INTERFACES_COLLECTION_H

#include "mlir/IR/Types.h"
#include <cstdint>
#include <optional>

namespace zkc {
/// Logical family identity, independent of learned extents or physical layout.
enum class CollectionKind {
  FieldVector,
  GroupVector,
  Indices,
  Bytes,
  FieldMatrix,
  FieldArray,
  FixedVector,
  Sequence
};
} // namespace zkc

#include "zkc/Interfaces/Collection.h.inc"

#endif
