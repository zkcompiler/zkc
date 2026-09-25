#ifndef ZKC_COMPILER_PIPELINES_H
#define ZKC_COMPILER_PIPELINES_H

#include "zkc/Protocol/PhysicalOptions.h"
#include "llvm/ADT/StringRef.h"
namespace mlir {
class OpPassManager;
}
namespace zkc {
/// Finite closed-source path. Empty physicalMode retains logical values.
void buildTablePipeline(mlir::OpPassManager &, bool simplify = false,
                        llvm::StringRef physicalMode = {});
/// Interactive path. Source-bound implementation selections must be checked
/// against the retained common source before projection, as in runCompiler.
void buildParticipantPipeline(mlir::OpPassManager &,
                              const protocol::PhysicalOptions & = {},
                              bool projectOnly = false);
/// Register named pipelines once; repeated calls are safe.
void registerCompilerPipelines();
} // namespace zkc
#endif
