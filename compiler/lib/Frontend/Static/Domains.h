#ifndef ZKC_FRONTEND_STATIC_DOMAINS_H
#define ZKC_FRONTEND_STATIC_DOMAINS_H

#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Domains.h"

namespace zkc::frontend {
/// Exact identities and lexical references remain distinct until common-term
/// serialization. An installed identity can only be an explicitly quoted root.
inline bool isDomainRoot(llvm::StringRef root, bool quoted) {
  return quoted ? !protocol::installedIdentitySort(root).empty()
                : !root.contains('.');
}
/// Common static terms resolve binders before exact installed identities. All
/// source owners must check this before erasing the identity/reference
/// category.
inline bool representableStaticBinder(
    llvm::StringRef name,
    const protocol::DomainCatalog &catalog = protocol::installedDomains()) {
  return !name.contains('.') && catalog.identitySort(name).empty();
}
} // namespace zkc::frontend
#endif
