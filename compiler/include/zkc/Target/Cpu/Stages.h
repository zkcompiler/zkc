#ifndef ZKC_TARGET_CPU_STAGES_H
#define ZKC_TARGET_CPU_STAGES_H
#include "zkc/Target/Cpu/Passes.h"
namespace zkc {
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
