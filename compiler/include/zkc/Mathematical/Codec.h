#ifndef ZKC_MATHEMATICAL_CODEC_H
#define ZKC_MATHEMATICAL_CODEC_H

#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"
#include <cstdint>
#include <string>
#include <vector>

namespace zkc::mathematical {

/// The v1 logical-tree limits. These bound the converted tree, including its
/// tags and scalar payload nodes. JSON has a separate transport byte limit.
struct EncodingLimits {
  static constexpr size_t bytes = 16 * 1024 * 1024;
  static constexpr size_t jsonBytes = 1024 * 1024;
  static constexpr size_t nodes = 200000;
  static constexpr size_t children = 32768;
  static constexpr unsigned depth = 64;
};

/// Structural value codecs only; none confers typed admission or registry
/// authority. Reject duplicate object keys before constructing an LLVM object.
llvm::Expected<llvm::json::Value> parseValue(llvm::StringRef text);
llvm::Expected<std::vector<uint8_t>> encodeValue(const llvm::json::Value &);
llvm::Expected<llvm::json::Value> decodeValue(llvm::ArrayRef<uint8_t> bytes);

/// Requires the exact three-field envelope and a known profile. Its module and
/// manifest still require independent semantic admission after digest checking.
llvm::Expected<std::string> subjectDigest(const llvm::json::Value &);

} // namespace zkc::mathematical
#endif
