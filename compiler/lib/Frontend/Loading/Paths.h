#ifndef ZKC_FRONTEND_LOADING_PATHS_H
#define ZKC_FRONTEND_LOADING_PATHS_H

#include "llvm/ADT/StringRef.h"
#include <algorithm>
#include <filesystem>

namespace zkc::frontend::loading {
inline bool contained(const std::filesystem::path &base,
                      const std::filesystem::path &path) {
  return std::mismatch(base.begin(), base.end(), path.begin(), path.end())
             .first == base.end();
}

inline bool relativeAsset(llvm::StringRef name) {
  if (name.empty() || name.size() > 4096 || name.contains('\\') ||
      name.contains('\0'))
    return false;
  std::filesystem::path path(name.str());
  if (path.is_absolute())
    return false;
  return std::none_of(path.begin(), path.end(),
                      [](const auto &part) { return part == ".."; });
}
} // namespace zkc::frontend::loading
#endif
