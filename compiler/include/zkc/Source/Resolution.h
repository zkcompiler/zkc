#ifndef ZKC_SOURCE_RESOLUTION_H
#define ZKC_SOURCE_RESOLUTION_H

#include "zkc/Source/Model.h"
#include "llvm/Support/Error.h"
#include <map>
#include <string>
#include <utility>

namespace zkc::source {

/// A checked copy with declaration-local sites in depth-first preorder.
/// Original source remains the custody subject. Maps are derived, not accepted
/// as producer evidence, and do not establish a cryptographic security theorem.
struct SiteResolution {
  Module source;
  std::map<std::pair<std::string, std::string>, std::string> functions;
  std::map<std::pair<std::string, std::string>, std::string> protocols;
  std::map<std::pair<std::string, std::string>, std::string> definitions;
  std::map<std::string, std::string> configurations;

  llvm::Expected<Construction> descriptor(const Construction &) const;
};

/// Admit the entire original source before renaming sites and using selectors.
/// Only explicit-binding common and generic-library sources are supported.
llvm::Expected<SiteResolution> resolveProtocolSites(const Module &);

} // namespace zkc::source

#endif
