#ifndef ZKC_FRONTEND_LOWERING_LIBRARY_SOURCE_H
#define ZKC_FRONTEND_LOWERING_LIBRARY_SOURCE_H

#include "../LibrarySource.h"
#include "zkc/Frontend/Library.h"
#include <map>
#include <set>

namespace zkc::frontend::resolution {
struct Context;
}

namespace zkc::frontend::lowering {
struct LibrarySource {
  syntax::Module ordinary;
  LibraryEmission generated;
};

/// Consume one link world, preserving shared resource identities and aliases.
/// This performs layout erasure, not source checking or common admission.
llvm::Expected<LibrarySource>
emitLibrarySource(syntax::Module, const library::Environment &,
                  llvm::ArrayRef<library::LinkedProgram>,
                  const std::map<std::string, source::Names> &entryAliases,
                  const std::set<std::string> &reservedNames,
                  const resolution::Context &, WorkBudget &);
} // namespace zkc::frontend::lowering
#endif
