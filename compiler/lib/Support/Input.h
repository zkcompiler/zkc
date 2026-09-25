#ifndef ZKC_SUPPORT_INPUT_H
#define ZKC_SUPPORT_INPUT_H
#include "llvm/Support/Error.h"
namespace zkc {
inline constexpr size_t sourceByteLimit = 1024 * 1024;
inline constexpr size_t mlirByteLimit = 64 * sourceByteLimit;
llvm::Expected<std::string> readInput(llvm::StringRef path, size_t byteLimit);
} // namespace zkc
#endif
