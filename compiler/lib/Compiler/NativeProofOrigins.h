#ifndef ZKC_LIB_COMPILER_NATIVE_PROOF_ORIGINS_H
#define ZKC_LIB_COMPILER_NATIVE_PROOF_ORIGINS_H
#include "llvm/ADT/StringMap.h"
#include "llvm/Support/Error.h"
#include <array>
#include <string>
#include <vector>
namespace zkc::mathematical {
class RealizedProtocol;
}
namespace zkc::detail {
struct NativeSourceOrigin {
  std::string protocol, site;
  std::vector<std::string> event;
  std::vector<std::array<std::string, 3>> steps;
};
// The record is read only through its immutable checked owner. Generated
// occurrences acquire source associations, never authority from helper names.
llvm::Expected<llvm::StringMap<NativeSourceOrigin>>
realizedNativeOrigins(const mathematical::RealizedProtocol &,
                      llvm::StringRef entry,
                      const llvm::StringMap<NativeSourceOrigin> &authored);
} // namespace zkc::detail
#endif
