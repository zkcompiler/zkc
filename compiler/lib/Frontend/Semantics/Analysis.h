#ifndef ZKC_FRONTEND_SEMANTICS_ANALYSIS_H
#define ZKC_FRONTEND_SEMANTICS_ANALYSIS_H
#include "../LibrarySource.h"
#include "../Model/Checked.h"
#include "../Syntax/Tree.h"
#include "zkc/Frontend/Analysis.h"
namespace zkc::frontend::model {
struct LibraryReport;
}
namespace zkc::frontend::instantiation {
struct Selection;
}
namespace zkc::frontend::semantics {

using SourceCheck =
    std::variant<std::unique_ptr<model::Module>, model::CheckedSource>;
/// Check a source model. Library judgments are retained
/// even when ordinary source checking fails. This does not admit common PIR.
SourceCheck checkStaged(const syntax::Content &original,
                        const instantiation::Selection &staged,
                        const LibraryEmission &linked,
                        std::shared_ptr<const model::LibraryReport> libraries,
                        std::shared_ptr<const resolution::Context> context,
                        llvm::StringRef text, llvm::StringRef filename,
                        bool resolutionComplete);
} // namespace zkc::frontend::semantics
#endif
