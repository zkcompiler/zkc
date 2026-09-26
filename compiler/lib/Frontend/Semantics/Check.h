#ifndef ZKC_FRONTEND_SEMANTICS_CHECK_H
#define ZKC_FRONTEND_SEMANTICS_CHECK_H

#include "../LibrarySource.h"
#include "../Model/Module.h"
#include "../Syntax/Tree.h"

namespace zkc::frontend::semantics {
llvm::Expected<model::Body> resolveBody(const model::Module &, DeclId,
                                        ScopeId operationScope,
                                        const source::Body &);
bool check(model::Module &, const syntax::Content &,
           const syntax::Content &original, const LibraryEmission &linked);
} // namespace zkc::frontend::semantics
#endif
