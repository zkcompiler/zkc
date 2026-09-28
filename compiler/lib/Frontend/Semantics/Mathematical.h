#ifndef ZKC_FRONTEND_SEMANTICS_MATHEMATICAL_H
#define ZKC_FRONTEND_SEMANTICS_MATHEMATICAL_H
#include "../Model/Module.h"
#include "../Syntax/Tree.h"
namespace zkc::frontend::semantics {
/// Build one closed mathematical entry using the already resolved bindings and
/// header types. Mathematical admission owns graph typing and availability.
bool buildMathematical(model::Module &, const syntax::Module &,
                       const source::Module &, WorkBudget &);
} // namespace zkc::frontend::semantics
#endif
