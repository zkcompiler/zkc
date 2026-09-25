#ifndef ZKC_COMPILER_SOURCE_H
#define ZKC_COMPILER_SOURCE_H
#include "zkc/Frontend/Analysis.h"
#include "zkc/Source/Document.h"
namespace mlir {
class MLIRContext;
}
namespace zkc {
/// Freeze emitted source with the same captured spelling and file ordinals.
/// Source checking and structural lowering do not imply common admission.
llvm::Expected<source::Document> lowerSource(const frontend::Analysis &);
/// Prepare source-name-preserving local specializations and SSA expansion.
/// The caller owns and initializes the MLIR context.
llvm::Expected<source::Content> prepareSource(const source::Document &,
                                              mlir::MLIRContext &);
} // namespace zkc
#endif
