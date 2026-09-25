#ifndef ZKC_FRONTEND_SEMANTICS_ANALYSIS_H
#define ZKC_FRONTEND_SEMANTICS_ANALYSIS_H
#include "../Lowering/LibrarySource.h"
#include "../Syntax/Tree.h"
#include "zkc/Frontend/Analysis.h"
namespace zkc::frontend::model {
struct LibraryReport;
}
namespace zkc::frontend::instantiation {
struct Selection;
}
namespace zkc::frontend::semantics {

/// Check and finalize an immutable analysis. Library judgments are retained
/// even when ordinary source checking fails. This does not admit common PIR.
Analysis analyzeStaged(const syntax::Content &original,
                       const instantiation::Selection &staged,
                       const lowering::LibraryEmission &linked,
                       std::shared_ptr<const model::LibraryReport> libraries,
                       llvm::StringRef text, llvm::StringRef filename,
                       bool resolutionComplete);
} // namespace zkc::frontend::semantics
#endif
