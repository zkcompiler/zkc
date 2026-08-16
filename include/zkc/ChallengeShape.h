//===- ChallengeShape.h - shared challenge multiplicity --------*- C++ -*-===//
//
// The carrier, endpoint IR, and protocol vocabulary share one bounded count
// domain. Keeping its parser here prevents a vector capability from being
// accepted by one layer and refused (or truncated) by another.
//
//===----------------------------------------------------------------------===//

#ifndef ZKC_CHALLENGESHAPE_H
#define ZKC_CHALLENGESHAPE_H

#include "llvm/ADT/StringRef.h"

#include <cstdint>
#include <optional>

namespace zkc {
namespace challenge {

/// Scalar sampling has count one. Vector sampling is bounded by 2^20, the
/// same resource ceiling used by protocol-vocabulary challenge uses.
inline constexpr uint64_t kMaxCount = uint64_t{1} << 20;

/// Whether `text` is the unique decimal spelling of a positive integer.
/// Challenge spaces are intentionally not machine-width bounded, so this
/// predicate is separate from `parseCount`.
inline bool isCanonicalPositiveDecimal(llvm::StringRef text) {
  if (text.empty() || text.front() == '0')
    return false;
  for (char c : text)
    if (c < '0' || c > '9')
      return false;
  return true;
}

/// Parse the one canonical carrier spelling of a challenge count. The result
/// is in [1, 2^20]; zero, leading zeros, non-decimal text, and overflow are
/// rejected rather than normalized.
/// The one spelling of the count-grammar refusal, shared by every op
/// that carries a count (squeeze, read, write, slot, hole results) so
/// the prose cannot drift between them; each site prefixes its own
/// diagnostic id.
inline constexpr const char kCountGrammarMessage[] =
    "count must be a canonical decimal from 1 through 2^20 (1 for scalar, "
    "2..2^20 for vector), got \"";

inline std::optional<uint64_t> parseCount(llvm::StringRef text) {
  if (!isCanonicalPositiveDecimal(text))
    return std::nullopt;
  uint64_t value = 0;
  if (text.getAsInteger(10, value) || value == 0 || value > kMaxCount)
    return std::nullopt;
  return value;
}

} // namespace challenge
} // namespace zkc

#endif // ZKC_CHALLENGESHAPE_H
