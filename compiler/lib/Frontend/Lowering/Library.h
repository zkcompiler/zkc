#ifndef ZKC_FRONTEND_LOWERING_LIBRARY_H
#define ZKC_FRONTEND_LOWERING_LIBRARY_H

#include "zkc/Frontend/Library.h"
#include <functional>

namespace zkc::frontend::library {
using OriginResolver = std::function<std::string(const QualifiedDecl &)>;
/// Lower only an immutable, coherently linked program. Aggregate projection is
/// resolved here, after opaque representations have been selected. Admission of
/// the returned portable module remains an independent boundary.
/// Close several checked clients in one link world. Shared dependency keys must
/// denote the same implementation; resource slot identities are allocated once.
llvm::Expected<source::Module> lower(llvm::ArrayRef<LinkedProgram>,
                                     OriginResolver, WorkBudget &);
} // namespace zkc::frontend::library
#endif
