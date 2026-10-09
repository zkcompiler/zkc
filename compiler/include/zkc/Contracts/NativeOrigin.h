#ifndef ZKC_CONTRACTS_NATIVEORIGIN_H
#define ZKC_CONTRACTS_NATIVEORIGIN_H
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include <array>
#include <string>
namespace zkc::protocol {
/// Bounded source occurrence syntax. Does not establish source correspondence.
llvm::Error checkNativeOrigin(llvm::StringRef hex, llvm::StringRef kind);
llvm::Expected<std::string>
encodeNativeOriginTemplate(llvm::StringRef entry,
                           llvm::ArrayRef<std::array<std::string, 3>> path,
                           llvm::ArrayRef<std::string> event);
} // namespace zkc::protocol
#endif
