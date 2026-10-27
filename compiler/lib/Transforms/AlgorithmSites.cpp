#include "zkc/Support/Json.h"
#include "zkc/Transforms/Algorithms.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"

using namespace llvm;
namespace zkc::protocol {
Expected<std::string> algorithmSite(const protocol::Assignments &path,
                                    StringRef site, uint64_t &remainingBytes) {
  uint64_t size = 2;
  auto measure = [&](StringRef value) {
    uint64_t prefix = 2 + std::to_string(value.size()).size();
    if (size > remainingBytes || prefix > remainingBytes - size ||
        value.size() > remainingBytes - size - prefix)
      return false;
    size += prefix + value.size();
    return true;
  };
  for (const auto &[call, callee] : path)
    if (!measure(call) || !measure(callee))
      return error("algorithm-origin-limit");
  if (!measure(site))
    return error("algorithm-origin-limit");
  remainingBytes -= size;
  std::string result = "lc";
  result.reserve(size);
  auto append = [&](StringRef value) {
    result += "_" + std::to_string(value.size()) + "_" + value.str();
  };
  for (const auto &[call, callee] : path) {
    append(call);
    append(callee);
  }
  append(site);
  if (result.size() > 128)
    return "lc_h_" + toHex(SHA256::hash(arrayRefFromStringRef(result)), true);
  return result;
}
} // namespace zkc::protocol
