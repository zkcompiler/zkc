#ifndef ZKC_FRONTEND_LIBRARY_SOURCE_H
#define ZKC_FRONTEND_LIBRARY_SOURCE_H
#include "Syntax/Tree.h"
namespace zkc::frontend {
/// Entry correspondence and generated library declarations. Entry adapters and
/// remaining authored declarations require ordinary source formation; linked
/// bodies retain the checked library's concrete types and representation plans.
struct LibraryEntry {
  syntax::Function header;
  source::Function forwarding;
  std::vector<source::Names> resultPaths;
};
struct LibraryEmission {
  source::Module module;
  std::vector<LibraryEntry> entries;
};
} // namespace zkc::frontend
#endif
