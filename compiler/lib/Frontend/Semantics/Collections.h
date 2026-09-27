#ifndef ZKC_FRONTEND_SEMANTICS_COLLECTIONS_H
#define ZKC_FRONTEND_SEMANTICS_COLLECTIONS_H

#include "llvm/ADT/StringRef.h"
#include <optional>
#include <string>

namespace zkc::frontend {
struct CollectionOperations {
  std::string index, length, empty, append;
};
inline std::optional<CollectionOperations>
collectionOperations(llvm::StringRef constructor) {
  llvm::StringRef prefix = constructor == "vector"    ? "vector"
                           : constructor == "groups"  ? "curve"
                           : constructor == "indices" ? "indices"
                                                      : "";
  if (prefix.empty())
    return std::nullopt;
  return CollectionOperations{prefix.str() +
                                  (constructor == "indices" ? ".at" : ".get"),
                              prefix.str() + ".length", prefix.str() + ".empty",
                              prefix.str() + ".append"};
}
} // namespace zkc::frontend
#endif
