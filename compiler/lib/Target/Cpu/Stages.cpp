#include "zkc/Target/Cpu/Stages.h"
#include "mlir/Pass/PassManager.h"
#include "zkc/Target/Cpu/Passes.h"
namespace zkc {
void buildPhysicalPipeline(mlir::OpPassManager &pm,
                           const PhysicalPipelineOptions &options) {
  pm.addPass(protocol::createSelectPhysicalPass(
      options.selections, options.linearContractions, options.releaseStorage,
      options.statistics, options.functionPorts, options.mathematics,
      options.cpuTarget));
}
} // namespace zkc
