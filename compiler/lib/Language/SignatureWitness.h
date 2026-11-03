#ifndef ZKC_LANGUAGE_SIGNATUREWITNESS_H
#define ZKC_LANGUAGE_SIGNATUREWITNESS_H
#include "State.h"
namespace zkc::language::detail {
/// Recheck callback contracts against independently retained authored syntax.
llvm::Error checkSignatureSources(const CheckedStorage &, Work &);
/// Reconstruct exact conformance edges from immutable authored headers, replay
/// signatures, and independently judge all implementation obligations.
llvm::Error checkModuleContracts(const CheckedStorage &, Work &);
} // namespace zkc::language::detail
#endif
