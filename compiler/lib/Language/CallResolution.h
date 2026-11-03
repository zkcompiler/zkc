#ifndef ZKC_LANGUAGE_CALLRESOLUTION_H
#define ZKC_LANGUAGE_CALLRESOLUTION_H
#include "Semantics.h"
#include "zkc/Language/DeclarationIndex.h"
namespace zkc::language::detail {
/// Select from canonical declarations, never imported namespace bindings.
/// Also used to reconstruct retained method calls independently.
std::optional<CallableReference>
resolveHomeMethod(Semantics &, llvm::ArrayRef<Declaration>,
                  const DeclarationIndex &, const Declaration &, const Type &,
                  llvm::StringRef, Span);
} // namespace zkc::language::detail
#endif
