#include "zkc/Language/Names.h"
#include <algorithm>
#include <cstring>
#include <limits>
#include <utf8proc.h>

using namespace llvm;

namespace zkc::language {
namespace {
struct Range {
  uint32_t first, last;
};
struct Delimiter {
  uint32_t opener, closer;
};
#include "SourceNameData.inc"

template <size_t N> bool contains(const Range (&ranges)[N], uint32_t scalar) {
  auto found = std::lower_bound(
      std::begin(ranges), std::end(ranges), scalar,
      [](const Range &range, uint32_t value) { return range.last < value; });
  return found != std::end(ranges) && found->first <= scalar;
}

bool validUTF8(StringRef text) {
  for (size_t offset = 0; offset < text.size();) {
    auto scalar = decodeSourceScalar(text, offset);
    if (!scalar)
      return false;
    offset += scalar->bytes;
  }
  return true;
}

bool scalarNFC(uint32_t scalar) {
  utf8proc_uint8_t bytes[4];
  auto size = utf8proc_encode_char(scalar, bytes);
  return size > 0 &&
         isSourceNFC(StringRef(reinterpret_cast<const char *>(bytes), size));
}

constexpr char hexDigits[] = "0123456789abcdef";
void appendHex(std::string &output, StringRef bytes) {
  for (unsigned char byte : bytes) {
    output += hexDigits[byte >> 4];
    output += hexDigits[byte & 15];
  }
}
int hexDigit(char byte) {
  if (byte >= '0' && byte <= '9')
    return byte - '0';
  if (byte >= 'a' && byte <= 'f')
    return byte - 'a' + 10;
  return -1;
}
std::string ordinalName(StringRef prefix, unsigned ordinal) {
  static_assert(std::numeric_limits<unsigned>::digits == 32);
  std::string result = prefix.str();
  for (unsigned shift = 32; shift != 0; shift -= 4)
    result += hexDigits[(ordinal >> (shift - 4)) & 15];
  return result;
}
} // namespace

std::optional<SourceScalar> decodeSourceScalar(StringRef text, size_t offset) {
  if (offset >= text.size())
    return std::nullopt;
  const auto *bytes =
      reinterpret_cast<const unsigned char *>(text.data() + offset);
  uint32_t value = bytes[0];
  if (value < 0x80)
    return SourceScalar{value, 1};
  size_t count;
  uint32_t minimum;
  if (value >= 0xc2 && value <= 0xdf) {
    count = 2;
    minimum = 0x80;
    value &= 0x1f;
  } else if (value >= 0xe0 && value <= 0xef) {
    count = 3;
    minimum = 0x800;
    value &= 0x0f;
  } else if (value >= 0xf0 && value <= 0xf4) {
    count = 4;
    minimum = 0x10000;
    value &= 0x07;
  } else {
    return std::nullopt;
  }
  if (count > text.size() - offset)
    return std::nullopt;
  for (size_t i = 1; i < count; ++i) {
    if ((bytes[i] & 0xc0) != 0x80)
      return std::nullopt;
    value = (value << 6) | (bytes[i] & 0x3f);
  }
  if (value < minimum || value > 0x10ffff ||
      (value >= 0xd800 && value <= 0xdfff))
    return std::nullopt;
  return SourceScalar{value, count};
}

bool sourceIdentifierStart(uint32_t scalar) {
  return contains(identifierStart, scalar);
}
bool sourceIdentifierContinue(uint32_t scalar) {
  return contains(identifierContinue, scalar);
}
bool isSourceIdentifier(StringRef text) {
  if (text.empty())
    return false;
  for (size_t offset = 0; offset < text.size();) {
    auto scalar = decodeSourceScalar(text, offset);
    if (!scalar || !(offset == 0 ? sourceIdentifierStart(scalar->value)
                                 : sourceIdentifierContinue(scalar->value)))
      return false;
    offset += scalar->bytes;
  }
  return isSourceNFC(text);
}

bool isSourceNFC(StringRef text) {
  // utf8proc takes a signed length and uses a UTF-32 intermediate. Bound its
  // worst-case canonical decomposition (at most four scalars per scalar),
  // including the terminating byte, before entering the allocator.
  constexpr auto maxLength =
      std::numeric_limits<utf8proc_ssize_t>::max() / (4 * sizeof(int32_t)) - 1;
  if (text.size() > maxLength)
    return false;
  if (std::all_of(text.begin(), text.end(),
                  [](unsigned char byte) { return byte < 0x80; }))
    return true;
  if (!validUTF8(text))
    return false;
  utf8proc_uint8_t *normalized = nullptr;
  auto size = utf8proc_map(
      reinterpret_cast<const utf8proc_uint8_t *>(text.data()), text.size(),
      &normalized, UTF8PROC_STABLE | UTF8PROC_COMPOSE);
  bool same = size >= 0 && static_cast<size_t>(size) == text.size() &&
              std::memcmp(normalized, text.data(), text.size()) == 0;
  utf8proc_free(normalized);
  return same;
}

bool isMathematicalSymbol(uint32_t scalar) {
  return contains(mathematicalSymbols, scalar) && scalarNFC(scalar);
}
std::optional<uint32_t> matchingSourceDelimiter(uint32_t opener) {
  auto found =
      std::lower_bound(std::begin(sourceDelimiters), std::end(sourceDelimiters),
                       opener, [](const Delimiter &pair, uint32_t value) {
                         return pair.opener < value;
                       });
  if (found == std::end(sourceDelimiters) || found->opener != opener ||
      !scalarNFC(opener) || !scalarNFC(found->closer))
    return std::nullopt;
  return found->closer;
}
bool isSourceDelimiterCloser(uint32_t scalar) {
  for (const auto &pair : sourceDelimiters)
    if (pair.closer == scalar)
      return matchingSourceDelimiter(pair.opener).has_value();
  return false;
}
std::string sourceNameProfileIdentity() { return sourceProfileIdentity; }

std::string nativeRoleName(unsigned ordinal) {
  return ordinalName("role", ordinal);
}
std::string nativeSetupName(unsigned ordinal) {
  return ordinalName("setup", ordinal);
}
std::string nativeAlternativeName(unsigned ordinal) {
  return ordinalName("case", ordinal);
}

std::string encodeNominalIdentity(StringRef text) {
  std::string result;
  // The caller owns this API's expansion limit. std::string still checks its
  // own capacity; avoid multiplying an unchecked size here.
  if (text.size() <= result.max_size() / 2)
    result.reserve(text.size() * 2);
  appendHex(result, text);
  return result;
}
std::optional<std::string> decodeNominalIdentity(StringRef hex,
                                                 uint64_t maxBytes) {
  if (hex.size() % 2 || hex.size() / 2 > maxBytes)
    return std::nullopt;
  // Validate spelling before allocating the decoded preimage.
  for (char byte : hex)
    if (hexDigit(byte) < 0)
      return std::nullopt;
  std::string result;
  if (hex.size() / 2 > result.max_size())
    return std::nullopt;
  result.reserve(hex.size() / 2);
  for (size_t offset = 0; offset < hex.size(); offset += 2)
    result += static_cast<char>((hexDigit(hex[offset]) << 4) |
                                hexDigit(hex[offset + 1]));
  if (!validUTF8(result))
    return std::nullopt;
  return result;
}

std::optional<std::string> encodeSourceSymbol(StringRef qualifiedName,
                                              uint64_t maxBytes) {
  std::string result;
  uint64_t limit = std::min<uint64_t>(maxBytes, result.max_size());
  if (limit < 1)
    return std::nullopt;
  uint64_t size = 1;
  StringRef rest = qualifiedName;
  while (true) {
    auto split = rest.split("::");
    StringRef segment = split.first;
    uint64_t digits = 1;
    for (size_t count = segment.size(); count >= 10; count /= 10)
      ++digits;
    uint64_t overhead = digits + 1;
    if (overhead > limit - size ||
        segment.size() > (limit - size - overhead) / 2)
      return std::nullopt;
    size += overhead + 2 * segment.size();
    if (!isSourceIdentifier(segment))
      return std::nullopt;
    if (rest.size() == segment.size())
      break;
    rest = split.second;
  }
  result.reserve(size);
  result += 's';
  rest = qualifiedName;
  while (true) {
    auto split = rest.split("::");
    result += std::to_string(split.first.size());
    result += 'h';
    appendHex(result, split.first);
    if (rest.size() == split.first.size())
      break;
    rest = split.second;
  }
  return result;
}
} // namespace zkc::language
