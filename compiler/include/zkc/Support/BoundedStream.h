#ifndef ZKC_SUPPORT_BOUNDEDSTREAM_H
#define ZKC_SUPPORT_BOUNDEDSTREAM_H

#include "llvm/Support/raw_ostream.h"
#include <cstdint>
#include <string>

namespace zkc {
/// Discards all further writes after a byte cap is exceeded. Callers must
/// inspect overflow() before publishing the accumulated bytes.
class BoundedStream : public llvm::raw_ostream {
public:
  BoundedStream(std::string &bytes, uint64_t limit)
      : bytes(bytes), limit(limit), exceeded(bytes.size() > limit) {
    SetUnbuffered();
  }
  bool overflow() const { return exceeded; }

private:
  std::string &bytes;
  uint64_t limit;
  bool exceeded;
  void write_impl(const char *data, size_t size) override {
    if (exceeded)
      return;
    if (size > limit - bytes.size()) {
      exceeded = true;
      return;
    }
    bytes.append(data, size);
  }
  uint64_t current_pos() const override { return bytes.size(); }
};
} // namespace zkc
#endif
