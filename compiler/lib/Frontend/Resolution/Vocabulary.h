#ifndef ZKC_FRONTEND_RESOLUTION_VOCABULARY_H
#define ZKC_FRONTEND_RESOLUTION_VOCABULARY_H
#include "../Static/Types.h"
#include "Names.h"
#include "zkc/Contracts/Bindings.h"
#include "llvm/ADT/STLExtras.h"

namespace zkc::frontend::resolution {
/// Core type words, available unless a lexical record or enum shadows them.
inline bool installedType(llvm::StringRef name) {
  return name == "Array" || name == "ResourceUnit" || name == "bool" ||
         name == "index";
}
/// Installed predicate words, available unless a lexical predicate shadows
/// them.
inline bool installedPredicate(llvm::StringRef name) {
  if (name == "=" || name == "nat" || name == "Nat" || name == "Type" ||
      name == "association")
    return true;
  generic::Signature signature;
  signature.requirements.push_back(
      requirements::Predicate::holds(name.str(), {}));
  auto error = protocol::checkStaticVocabulary(signature);
  return !error ||
         llvm::toString(std::move(error)) != "generic-declared-predicate";
}
/// Installed data a quoted static or type atom may name: an installed identity,
/// or in a type position a closed wire type spelling.
inline bool installedExact(llvm::StringRef value, ReferenceKind kind) {
  if (kind == ReferenceKind::Type) {
    auto parsed = protocol::parseBoundType(value, false);
    if (parsed)
      return true;
    llvm::consumeError(parsed.takeError());
  }
  return (kind == ReferenceKind::Static || kind == ReferenceKind::Type) &&
         !protocol::installedIdentitySort(value).empty();
}
} // namespace zkc::frontend::resolution
#endif
