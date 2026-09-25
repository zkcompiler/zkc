#ifndef ZKC_FRONTEND_SEMANTICS_CHECK_H
#define ZKC_FRONTEND_SEMANTICS_CHECK_H

#include "../Model/Module.h"
#include "../Syntax/Tree.h"
#include "zkc/Frontend/Analysis.h"

namespace zkc::frontend::instantiation {
struct Selection;
}
namespace zkc::frontend::semantics {
llvm::Expected<model::Body> resolveBody(const model::Module &, DeclId,
                                        ScopeId operationScope,
                                        const source::Body &);
void check(model::Module &, const syntax::Content &,
           const syntax::Content &original);
Analysis analyzeStaged(const syntax::Content &original,
                       const instantiation::Selection &staged,
                       llvm::StringRef text, llvm::StringRef filename,
                       llvm::ArrayRef<Diagnostic> diagnostics = {});
} // namespace zkc::frontend::semantics
#endif
