#ifndef ZKC_FRONTEND_SEMANTICS_PROVENANCE_H
#define ZKC_FRONTEND_SEMANTICS_PROVENANCE_H
#include "../Model/Module.h"
namespace zkc::frontend::semantics {
/// Finalize query provenance from resolution and checking without changing
/// keys.
void retainQueryMetadata(model::Module &);
} // namespace zkc::frontend::semantics
#endif
