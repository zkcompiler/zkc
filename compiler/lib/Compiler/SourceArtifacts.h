#ifndef ZKC_COMPILER_SOURCEARTIFACTS_H
#define ZKC_COMPILER_SOURCEARTIFACTS_H
#include "zkc/Compiler/Language.h"
#include "llvm/Support/JSON.h"
namespace zkc::language::detail {
/// The existing original/interface association, shared by source publications.
/// There is no second admitted-subject identity for auxiliary proposals.
llvm::json::Object sourceAdmission(const CheckedOriginal &);
} // namespace zkc::language::detail
#endif
