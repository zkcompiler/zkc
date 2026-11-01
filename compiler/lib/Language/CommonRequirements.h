#ifndef ZKC_LANGUAGE_COMMONREQUIREMENTS_H
#define ZKC_LANGUAGE_COMMONREQUIREMENTS_H
#include "State.h"
namespace zkc::language::detail {
/// Validate common-control formation before publishing checked bodies. Uses the
/// caller's complete work budget; input obligations remain admission work.
llvm::Error checkCommonControlRequirements(const std::vector<Declaration> &,
                                           llvm::ArrayRef<Asset>, Work &);
llvm::Error checkCommonControlRequirements(const ClosedEntry &, Work &);
} // namespace zkc::language::detail
#endif
