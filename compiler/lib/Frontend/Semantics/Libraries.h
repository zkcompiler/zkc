#ifndef ZKC_FRONTEND_SEMANTICS_LIBRARIES_H
#define ZKC_FRONTEND_SEMANTICS_LIBRARIES_H
#include "../Syntax/Tree.h"
#include "zkc/Frontend/Library.h"
namespace zkc::frontend::semantics {
struct LibraryReport {
  source::Module lowered;
  struct Association {
    std::string name, kind, subject;
  };
  std::vector<Association> associations;
  std::vector<std::pair<std::string, library::Interface>> interfaces;
  std::vector<std::pair<std::string, library::CheckedBody>> clients;
  std::vector<std::pair<std::string, library::CheckedComponent>> components;
  std::vector<std::pair<std::string, library::CheckedBody>> componentBodies;
  std::vector<std::pair<std::string, library::LinkedProgram>> links;
};
bool hasLibraries(const syntax::Module &);
// Checks abstract clients before selecting representations. Only closed lowered
// functions are returned to the ordinary source/PIR frontend.
llvm::Expected<syntax::Module>
integrateLibraries(const syntax::Module &, llvm::StringRef text,
                   llvm::StringRef filename,
                   std::shared_ptr<const LibraryReport> *report = nullptr);
} // namespace zkc::frontend::semantics
#endif
