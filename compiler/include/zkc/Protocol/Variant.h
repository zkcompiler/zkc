#ifndef ZKC_PROTOCOL_VARIANT_H
#define ZKC_PROTOCOL_VARIANT_H
#include "llvm/Support/JSON.h"
#include <optional>
#include <string>
#include <string_view>
#include <vector>
namespace zkc::protocol {
struct VariantAlternative {
  std::string label;
  std::vector<std::string> payload;
};
struct VariantDescriptor {
  llvm::json::Value nominal;
  std::vector<VariantAlternative> alternatives;
};
inline constexpr size_t VariantSpellingBytes = 256 * 1024;
/// Logical, self-contained nominal identity. Both directions check formation,
/// canonical spelling and bounded recursive payloads; physical types are
/// refused.
std::optional<VariantDescriptor> decodeVariant(std::string_view);
std::optional<std::string> encodeVariant(const VariantDescriptor &);
} // namespace zkc::protocol
#endif
