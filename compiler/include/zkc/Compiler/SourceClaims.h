#ifndef ZKC_COMPILER_SOURCECLAIMS_H
#define ZKC_COMPILER_SOURCECLAIMS_H
#include "zkc/Compiler/Language.h"

namespace zkc::language {
/// Wire claims and exact original/interface references for one checked Entry.
/// The original SHA256 and protocol symbol match protocol-structured's input
/// reference. Lean must resolve the admitted-unit digest and registry meanings.
llvm::Expected<std::string> exportSourceClaims(const CheckedOriginal &,
                                               const Limits & = {});
/// Exact structural comparison, with unique JSON keys and bounded naturals.
llvm::Error checkSourceClaims(const CheckedOriginal &, llvm::StringRef,
                              const Limits & = {});
} // namespace zkc::language
#endif
