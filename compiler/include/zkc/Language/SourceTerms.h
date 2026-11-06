#ifndef ZKC_LANGUAGE_SOURCETERMS_H
#define ZKC_LANGUAGE_SOURCETERMS_H
#include "zkc/Language/Project.h"
#include "llvm/Support/JSON.h"

namespace zkc::language {
/// Encode a closed source term using the public, kind-preserving tree grammar.
/// Closed Formal constructors are ordinary terms; unbound Parameters are not.
llvm::Expected<llvm::json::Value> encodeStaticTerm(const Type &);
/// Validate and debit the caller's cumulative allowance before allocating the
/// source tree. The default entry above has its own bounded allowance.
llvm::Expected<llvm::json::Value> encodeStaticTerm(const Type &, const Limits &,
                                                   uint64_t remaining,
                                                   TypeWorkCharge);
llvm::Expected<llvm::json::Value> encodeProtocolOrigin(const ClosedEntry &,
                                                       const Declaration &);
} // namespace zkc::language
#endif
