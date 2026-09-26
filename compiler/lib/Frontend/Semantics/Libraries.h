#ifndef ZKC_FRONTEND_SEMANTICS_LIBRARIES_H
#define ZKC_FRONTEND_SEMANTICS_LIBRARIES_H
#include "../Model/Libraries.h"
#include "../Syntax/Tree.h"
#include <set>
namespace zkc::frontend::resolution {
struct Context;
}

namespace zkc::frontend::semantics {
struct LinkedLibrarySource {
  syntax::Module ordinary;
  library::Environment environment;
  std::vector<library::LinkedProgram> programs;
  std::map<std::string, source::Names> entryAliases;
  std::set<std::string> reservedNames;
};
bool hasLibraries(const syntax::Module &);
/// The result and retained judgments share one lifetime contract. Failed
/// elaboration still exposes the interfaces/bodies checked before the failure.
struct LibraryElaboration {
  llvm::Expected<LinkedLibrarySource> content;
  std::shared_ptr<const model::LibraryReport> report;
};
LibraryElaboration elaborateLibraries(const syntax::Module &,
                                      const resolution::Context &,
                                      llvm::StringRef text,
                                      llvm::StringRef filename, WorkBudget &);
} // namespace zkc::frontend::semantics
#endif
