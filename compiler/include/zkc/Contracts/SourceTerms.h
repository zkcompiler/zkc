#ifndef ZKC_CONTRACTS_SOURCETERMS_H
#define ZKC_CONTRACTS_SOURCETERMS_H
#include "llvm/Support/JSON.h"

namespace zkc {
/// Public static-term syntax, independent of compiler type hashes and layouts.
/// Validation is bounded by 64 levels, 4096 terms, 512-byte strings and 128
/// named arguments. Only the protocol template path has a 2048-byte allowance.
llvm::Error checkStaticTerm(const llvm::json::Value &);
llvm::Error checkProtocolOrigin(const llvm::json::Value &);
} // namespace zkc
#endif
