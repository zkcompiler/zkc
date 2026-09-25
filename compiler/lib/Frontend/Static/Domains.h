#ifndef ZKC_FRONTEND_STATIC_DOMAINS_H
#define ZKC_FRONTEND_STATIC_DOMAINS_H

#include "zkc/Protocol/Bindings.h"

namespace zkc::frontend {
/// Dotted spellings name installed identities, never implicit projections.
/// Associated members come only from explicit :: syntax. A quoted root cannot
/// name a bound parameter. Apply this before converting a source path into the
/// common carrier's dotted term spelling.
inline bool isDomainRoot(llvm::StringRef root, bool quoted) {
  return !protocol::installedIdentitySort(root).empty() ||
         (!quoted && !root.contains('.'));
}
} // namespace zkc::frontend
#endif
