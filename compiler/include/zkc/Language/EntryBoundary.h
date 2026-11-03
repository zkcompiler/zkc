#ifndef ZKC_LANGUAGE_ENTRYBOUNDARY_H
#define ZKC_LANGUAGE_ENTRYBOUNDARY_H
#include "zkc/Language/Layout.h"
namespace zkc::language {
/// True for the same subtree or an ancestor. Roles are compared separately.
bool entryPathContains(unsigned port, llvm::ArrayRef<unsigned> path,
                       unsigned selectedPort,
                       llvm::ArrayRef<unsigned> selected);
/// Allocate readable aliases in coordinate order, reserving whole-port names.
/// Names are display data; callers retain the exact selection independently.
llvm::Expected<std::vector<std::string>>
entrySelectionAliases(llvm::ArrayRef<EntryInputSelection>,
                      llvm::ArrayRef<std::string> candidates,
                      uint64_t &remaining);
} // namespace zkc::language
#endif
