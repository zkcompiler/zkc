#ifndef ZKC_SUPPORT_FRAMEDHASH_H
#define ZKC_SUPPORT_FRAMEDHASH_H
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
namespace zkc {
/// SHA-256 of length-prefixed byte strings (unsigned 64-bit little endian).
/// Charge all input bytes against the caller's phase budget; retain no input.
class FramedHash {
  llvm::SHA256 hash;
  uint64_t &remaining;
  bool limited = false;

public:
  explicit FramedHash(uint64_t &remaining) : remaining(remaining) {}
  void frame(llvm::StringRef value) {
    if (limited || remaining < 8 || value.size() > remaining - 8) {
      limited = true;
      return;
    }
    remaining -= 8 + value.size();
    uint8_t size[8];
    for (unsigned i = 0; i < 8; ++i)
      size[i] = uint64_t(value.size()) >> (8 * i);
    hash.update(size);
    hash.update(value);
  }
  llvm::Expected<std::string> finish() {
    if (limited)
      return error("source.limit", "identity work limit exceeded");
    return llvm::toHex(hash.final(), true);
  }
};
} // namespace zkc
#endif
