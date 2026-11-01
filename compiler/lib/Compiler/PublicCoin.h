#ifndef ZKC_COMPILER_OWNED_PUBLIC_COIN_H
#define ZKC_COMPILER_OWNED_PUBLIC_COIN_H
#include "../Transforms/RealizedProtocol.h"
#include "llvm/Support/JSON.h"
namespace zkc::detail {
// Analyze snapshots from the compilation's existing checked owner. No second
// preparation and no independently supplied policy can disagree with it.
llvm::Expected<llvm::json::Value>
analyzePublicCoin(const mathematical::RealizedProtocol &, llvm::StringRef);
} // namespace zkc::detail
#endif
