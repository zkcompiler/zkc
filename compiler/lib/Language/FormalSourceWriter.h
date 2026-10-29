#ifndef ZKC_LANGUAGE_FORMALSOURCEWRITER_H
#define ZKC_LANGUAGE_FORMALSOURCEWRITER_H
#include "FormalSource.h"
#include "llvm/Support/JSON.h"
#include <functional>
namespace zkc::language::detail {
// The owning writer supplies path allocation, work limits and error handling.
using FormalEmit = std::function<llvm::json::Value(
    llvm::StringRef, source::Span, llvm::json::Object)>;
using FormalChild = std::function<llvm::json::Value(
    llvm::StringRef, unsigned, std::function<llvm::json::Value()>)>;
llvm::json::Value writeFormalSource(const FormalSource &, const FormalEmit &,
                                    const FormalChild &);
} // namespace zkc::language::detail
#endif
