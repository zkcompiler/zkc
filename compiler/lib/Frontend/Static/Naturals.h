#ifndef ZKC_FRONTEND_STATIC_NATURALS_H
#define ZKC_FRONTEND_STATIC_NATURALS_H
#include "../Syntax/Tree.h"
#include "zkc/Frontend/Input.h"
#include "zkc/Frontend/Work.h"
namespace zkc::frontend::static_eval {
/// Pure, bounded natural evaluation. Cached dependency heights make the depth
/// limit independent of declaration order. No provider, I/O, or runtime calls.
llvm::Expected<std::map<std::string, uint64_t>>
evaluateNaturals(llvm::ArrayRef<syntax::Constant>, llvm::StringRef text,
                 llvm::StringRef filename, const ProjectInput *, WorkBudget &);
} // namespace zkc::frontend::static_eval
#endif
