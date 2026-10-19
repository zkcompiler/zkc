#ifndef ZKC_TEST_SUPPORT_SOURCE_PROJECT_H
#define ZKC_TEST_SUPPORT_SOURCE_PROJECT_H

#include "NativeCases.h"
#include "zkc/Language/Project.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/MemoryBuffer.h"

namespace zkc::test {
/// Configure-time input selection shares the maintained project manifest.
/// Source bytes remain runtime inputs so edits do not require reconfiguration.
inline std::vector<language::SourceBuffer> sourceProject(llvm::StringRef path) {
  auto read = [](llvm::StringRef source) {
    auto buffer = llvm::MemoryBuffer::getFile(source);
    require(bool(buffer), "cannot read source project input " + source);
    return (*buffer)->getBuffer().str();
  };
  auto value = take(llvm::json::parse(read(path)));
  auto *modules = value.getAsObject();
  require(modules != nullptr, "source project must contain a module map");
  std::vector<language::SourceBuffer> sources;
  for (const auto &entry : *modules) {
    auto source = entry.second.getAsString();
    require(source.has_value(), "source project path must be a string");
    sources.push_back({entry.first.str(), read(*source), source->str()});
  }
  llvm::sort(sources, [](const auto &left, const auto &right) {
    return left.module < right.module;
  });
  return sources;
}
} // namespace zkc::test
#endif
