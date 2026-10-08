#ifndef ZKC_COMPILER_LANGUAGEPACKAGE_H
#define ZKC_COMPILER_LANGUAGEPACKAGE_H
#include "zkc/Compiler/Language.h"
namespace zkc::language {
inline constexpr uint64_t entryPackageByteLimit = 64 * 1024 * 1024;
/// Immutable publication bytes. The application must authorize identity()
/// independently; a digest received alongside these bytes is not authority.
class EntryPackage {
public:
  llvm::StringRef bytes() const { return encoded; }
  llvm::StringRef identity() const { return digest; }

private:
  std::string encoded, digest;
  EntryPackage(std::string encoded, std::string digest)
      : encoded(std::move(encoded)), digest(std::move(digest)) {}
  friend llvm::Expected<EntryPackage> packageEntry(const CompiledEntry &,
                                                   uint64_t);
};
/// Capture the exact checked original, interface, selected deployment and
/// compilation choices in one package. The byte limit can only be lowered.
/// Runtime input values and secret setup/provider state are never included.
llvm::Expected<EntryPackage>
packageEntry(const CompiledEntry &, uint64_t byteLimit = entryPackageByteLimit);
} // namespace zkc::language
#endif
