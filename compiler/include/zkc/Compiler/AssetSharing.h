#ifndef ZKC_COMPILER_ASSET_SHARING_H
#define ZKC_COMPILER_ASSET_SHARING_H

#include "zkc/Language/Assets.h"
#include "llvm/ADT/ArrayRef.h"
#include <cstdint>
#include <vector>

namespace zkc::language {
struct SharedAsset {
  Asset asset;
  /// One node map for a ring asset, or one per relation table in table order.
  std::vector<std::vector<uint32_t>> nodeMaps;
  bool changed = false;
};

/// Produce a new canonical mathematical asset with identical nodes shared.
/// Bundle bindings, scopes, authorities and interactions are preserved. The
/// result is checked before return; compilation captures it under its new
/// identity. This does not mutate an existing capture or Entry publication.
llvm::Expected<SharedAsset> shareAsset(const Asset &);

/// Independently check expression sharing and exact surrounding Bundle data.
/// Names and diagnostic paths do not participate in mathematical identity.
llvm::Error checkAssetSharing(const Asset &original, const Asset &candidate,
                              llvm::ArrayRef<std::vector<uint32_t>> nodeMaps);
} // namespace zkc::language
#endif
