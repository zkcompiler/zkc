#ifndef ZKC_COMPILER_IRFINGERPRINT_H
#define ZKC_COMPILER_IRFINGERPRINT_H
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
namespace zkc::detail {
/// Bounded identity of the actual printed subject, without an extra IR copy.
inline llvm::Expected<std::string> fingerprintIR(mlir::ModuleOp module,
                                                 llvm::StringRef limitCode) {
  class Stream final : public llvm::raw_ostream {
    llvm::SHA256 hash;
    uint64_t bytes = 0;
    void write_impl(const char *data, size_t size) override {
      bytes += size;
      if (bytes <= 16 * 1024 * 1024)
        hash.update(llvm::StringRef(data, size));
    }
    uint64_t current_pos() const override { return bytes; }

  public:
    Stream() { SetBufferSize(4096); }
    ~Stream() override { flush(); }
    llvm::Expected<std::string> finish(llvm::StringRef code) {
      flush();
      if (bytes > 16 * 1024 * 1024)
        return error(code);
      return llvm::toHex(hash.final(), true);
    }
  } stream;
  module.print(stream);
  return stream.finish(limitCode);
}
} // namespace zkc::detail
#endif
