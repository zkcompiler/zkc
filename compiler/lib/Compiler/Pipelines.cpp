#include "zkc/Compiler/Pipelines.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Pass/PassRegistry.h"
#include "zkc/Transforms/Passes.h"

namespace zkc {
void buildTablePipeline(mlir::OpPassManager &pm, bool simplify,
                        llvm::StringRef physicalMode) {
  if (simplify)
    pm.addPass(createSimplifyTableRegionsPass());
  pm.addPass(createLowerPIRToPlanPass());
  if (!physicalMode.empty())
    pm.addPass(createLowerPlanToPhysicalPass(physicalMode));
}
void buildParticipantPipeline(mlir::OpPassManager &pm,
                              const protocol::PhysicalOptions &options,
                              bool projectOnly,
                              LinearContractionStats *statistics) {
  pm.addPass(protocol::createProjectParticipantsPass());
  if (!projectOnly)
    pm.addPass(protocol::createPlanParticipantsPass(
        options.implementations.choices, options.linearContractions,
        options.releaseStorage, statistics));
}
namespace {
struct TableOptions : mlir::PassPipelineOptions<TableOptions> {
  Option<bool> simplify{*this, "simplify", llvm::cl::init(false),
                        llvm::cl::desc("Simplify identical table endpoints")};
  Option<std::string> physical{*this, "physical", llvm::cl::init(""),
                               llvm::cl::desc("Empty, lazy or materialized")};
};
struct ParticipantOptions : mlir::PassPipelineOptions<ParticipantOptions> {
  Option<bool> projectOnly{*this, "project-only", llvm::cl::init(false),
                           llvm::cl::desc("Stop after participant projection")};
  Option<bool> linear{
      *this, "linear-contractions", llvm::cl::init(false),
      llvm::cl::desc("Select eligible local diagonal contractions")};
  Option<bool> release{*this, "release-storage", llvm::cl::init(false),
                       llvm::cl::desc("Release local storage after last use")};
};
} // namespace
void registerCompilerPipelines() {
  static mlir::PassPipelineRegistration<TableOptions> tables(
      "zkc-table-pipeline", "Lower a finite closed-source program",
      [](mlir::OpPassManager &pm, const TableOptions &options) {
        buildTablePipeline(pm, options.simplify, options.physical);
      });
  static mlir::PassPipelineRegistration<ParticipantOptions> participants(
      "zkc-participant-pipeline", "Project and plan an interactive protocol",
      [](mlir::OpPassManager &pm, const ParticipantOptions &options) {
        protocol::PhysicalOptions physical;
        physical.linearContractions = options.linear;
        physical.releaseStorage = options.release;
        buildParticipantPipeline(pm, physical, options.projectOnly);
      });
}
} // namespace zkc
