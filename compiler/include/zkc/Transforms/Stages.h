#ifndef ZKC_TRANSFORMS_STAGES_H
#define ZKC_TRANSFORMS_STAGES_H

#include "zkc/Transforms/Passes.h"
namespace mlir {
class OpPassManager;
}
namespace zkc {
/// Shared stage construction for production and textual pipelines. Each
/// transformation admits its actual input and candidate; callers retain the
/// immutable source separately when checking a source-relative crossing.
void buildPreparationPipeline(mlir::OpPassManager &, bool simplify = true,
                              MathematicalSelectionPolicy = {},
                              mathematical::RealizationTrace * = nullptr);
void buildProjectionPipeline(mlir::OpPassManager &, bool simplify = true,
                             MathematicalSelectionPolicy = {});
void buildExecutionPipeline(mlir::OpPassManager &, bool simplify = false,
                            bool fixPolynomials = false,
                            MathematicalSelectionPolicy = {},
                            mathematical::RealizationTrace * = nullptr);
/// Close the participant deployment by one checked scoped expansion and helper
/// pruning, then form executable computations. Use for native compilation and
/// the full textual participant pipeline, not standalone mathematical
/// rewriting.
void buildClosedExecutionPipeline(mlir::OpPassManager &, bool simplify = false,
                                  bool fixPolynomials = false,
                                  MathematicalSelectionPolicy = {},
                                  mathematical::RealizationTrace * = nullptr);
struct PhysicalPipelineOptions {
  protocol::Assignments selections;
  llvm::SmallVector<target::FunctionPortSelection> functionPorts;
  target::CpuTarget cpuTarget;
  MathematicalSelectionPolicy mathematics;
  bool linearContractions = false;
  bool releaseStorage = false;
  LinearContractionStats *statistics = nullptr;
};
void buildPhysicalPipeline(mlir::OpPassManager &,
                           const PhysicalPipelineOptions & = {});
} // namespace zkc
#endif
