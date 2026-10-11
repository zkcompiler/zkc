#ifndef ZKC_LANGUAGE_SIGNATUREWITNESS_H
#define ZKC_LANGUAGE_SIGNATUREWITNESS_H
#include "State.h"
namespace zkc::language::detail {
/// Recheck callback contracts against independently retained authored syntax.
llvm::Error checkSignatureSources(const CheckedStorage &, Work &);
/// Check implementation effects against interface contracts after body checks.
llvm::Error checkComponentEffects(const CheckedStorage &, Work &);
} // namespace zkc::language::detail
#endif
