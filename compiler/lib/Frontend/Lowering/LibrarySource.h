#ifndef ZKC_FRONTEND_LOWERING_LIBRARY_SOURCE_H
#define ZKC_FRONTEND_LOWERING_LIBRARY_SOURCE_H

#include "../Syntax/Tree.h"
#include "zkc/Frontend/Library.h"
#include <map>
#include <set>

namespace zkc::frontend::lowering {
/// Distinct products of library elaboration. Entry adapters and remaining
/// authored declarations require ordinary source formation; linked bodies
/// retain the checked library's concrete types and representation plans.
struct LibraryEntry {
  syntax::Function header;
  source::Function forwarding;
  std::vector<source::Names> resultPaths;
};
struct LibraryEmission {
  source::Module module;
  std::vector<LibraryEntry> entries;
};
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
                  const std::set<std::string> &reservedNames);
} // namespace zkc::frontend::lowering
#endif
