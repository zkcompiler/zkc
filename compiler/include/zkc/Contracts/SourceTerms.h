#ifndef ZKC_CONTRACTS_SOURCETERMS_H
#define ZKC_CONTRACTS_SOURCETERMS_H
#include "llvm/Support/JSON.h"

namespace zkc {
/// Public static-term syntax, independent of compiler type hashes and layouts.
/// Validation is bounded by 64 levels, 4096 terms, 512 children per list,
/// 512-byte strings and 128 named arguments. Only the protocol template path
/// has a 2048-byte allowance. Structural descriptor children use the closed
/// descriptor subgrammar: Product, Sequence, or the exact primitive Finite
/// leaf. This recognizes wire syntax, not checked source formation, installed
/// authority or native interpretation.
llvm::Error checkStaticTerm(const llvm::json::Value &);
llvm::Error checkProtocolOrigin(const llvm::json::Value &);
/// Semantic path grammar and NFC, independent of an enclosing wire capacity.
bool staticTermPath(llvm::StringRef);
} // namespace zkc
#endif
