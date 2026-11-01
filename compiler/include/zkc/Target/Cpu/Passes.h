#ifndef ZKC_TARGET_CPU_PASSES_H
#define ZKC_TARGET_CPU_PASSES_H
#include "zkc/Target/Selection.h"
#include "zkc/Transforms/Passes.h"
namespace zkc {
void registerCpuPasses();
void registerCpuPipelines();
namespace protocol {
/// Select representations and kernels, converting exec to physical.
/// Selections have already been checked against the caller's retained source.
std::unique_ptr<mlir::Pass> createSelectPhysicalPass(
    protocol::Assignments selections = {}, bool linearContractions = false,
    bool releaseStorage = false, LinearContractionStats *statistics = nullptr,
    llvm::ArrayRef<target::FunctionPortSelection> functionPorts = {},
    MathematicalSelectionPolicy numericalPolicy = {},
    const target::CpuTarget &cpuTarget = {});
} // namespace protocol
} // namespace zkc
#endif
