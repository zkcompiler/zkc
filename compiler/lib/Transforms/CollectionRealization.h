#ifndef ZKC_TRANSFORMS_COLLECTIONREALIZATION_H
#define ZKC_TRANSFORMS_COLLECTIONREALIZATION_H

#include "mlir/IR/Types.h"
#include "zkc/Contracts/Binding.h"
#include <cstdint>
#include <optional>

namespace zkc::mathematical {
/// Closed producer recipe inventory, separate from collection observation.
/// Each application names a declaration-owned contract; candidate admission
/// checks its resolved ports and parameters. Missing actions are unavailable.
struct CollectionRealization {
  mlir::Type element, storage;
  unsigned rank;
  std::optional<uint64_t> staticExtent;
  std::optional<protocol::BindingApplication> length, get, empty, append, wrap;
};

/// Existing finite collection families only. Bytes and FixedVector observation
/// do not grant finite collection admission. Field arrays collect in dynamic
/// field-vector storage, then wrap through their exact declared array length.
std::optional<CollectionRealization> collectionRealization(mlir::Type);
} // namespace zkc::mathematical

#endif
