#ifndef ZKC_CONTRACTS_VARIANT_H
#define ZKC_CONTRACTS_VARIANT_H
#include "llvm/Support/JSON.h"
#include <optional>
#include <string>
#include <string_view>
#include <vector>
namespace zkc::protocol {
struct TypeParseBudget;
struct VariantAlternative {
  std::string label;
  std::vector<std::string> payload;
};
struct VariantDescriptor {
  llvm::json::Value nominal;
  std::vector<VariantAlternative> alternatives;
};
inline constexpr size_t VariantSpellingBytes = 256 * 1024;
/// The portable descriptor's own alternative limit: the largest power of two
/// for which a variant with that many alternatives can still be spelled within
/// the program format's 4,096-byte type string. MLIR formation admits wider
/// variants; spelling one refuses here.
inline constexpr size_t VariantDescriptorAlternatives = 64;
/// Logical, self-contained nominal identity. Both directions check formation,
/// canonical spelling and bounded recursive payloads; physical types are
/// refused.
std::optional<VariantDescriptor>
decodeVariant(std::string_view, unsigned depth = 0,
              TypeParseBudget *budget = nullptr);
std::optional<std::string> encodeVariant(const VariantDescriptor &);
} // namespace zkc::protocol
#endif
