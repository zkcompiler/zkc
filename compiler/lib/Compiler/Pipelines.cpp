#include "zkc/Compiler/Pipelines.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Pass/PassRegistry.h"
#include "zkc/Transforms/Passes.h"

namespace zkc {
namespace {
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
  static mlir::PassPipelineRegistration<ParticipantOptions> participants(
      "zkc-participant-pipeline", "Project and plan an interactive protocol",
      [](mlir::OpPassManager &pm, const ParticipantOptions &options) {
        pm.addPass(protocol::createProjectProtocolPass());
        if (!options.projectOnly) {
          pm.addPass(protocol::createEliminatePolynomialsPass());
          pm.addPass(protocol::createLowerMathPass());
          pm.addPass(protocol::createSelectPhysicalPass({}, options.linear,
                                                        options.release));
        }
      });
}
} // namespace zkc
