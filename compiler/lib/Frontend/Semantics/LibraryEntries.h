#ifndef ZKC_FRONTEND_SEMANTICS_LIBRARY_ENTRIES_H
#define ZKC_FRONTEND_SEMANTICS_LIBRARY_ENTRIES_H
#include "../LibrarySource.h"

namespace zkc::frontend::semantics {
/// Match an entry's linked layout to independently formed source ports and its
/// internal target. This checks correspondence, not constructor authority or
/// common admission. A generated entry receives no exemption from these checks.
llvm::Error checkLibraryEntry(const LibraryEntry &,
                              const source::Function &formed,
                              llvm::ArrayRef<source::Names> resultPaths,
                              const source::Function &target);
} // namespace zkc::frontend::semantics
#endif
