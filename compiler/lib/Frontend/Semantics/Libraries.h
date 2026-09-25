#ifndef ZKC_FRONTEND_SEMANTICS_LIBRARIES_H
#define ZKC_FRONTEND_SEMANTICS_LIBRARIES_H
#include "../Lowering/LibrarySource.h"
#include "../Model/Libraries.h"
namespace zkc::frontend::semantics {
bool hasLibraries(const syntax::Module &);
/// The result and retained judgments share one lifetime contract. Failed
/// elaboration still exposes the interfaces/bodies checked before the failure.
struct LibraryElaboration {
  llvm::Expected<lowering::LibrarySource> content;
  std::shared_ptr<const model::LibraryReport> report;
};
LibraryElaboration elaborateLibraries(const syntax::Module &,
                                      llvm::StringRef text,
                                      llvm::StringRef filename);
} // namespace zkc::frontend::semantics
#endif
