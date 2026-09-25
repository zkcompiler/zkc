#include "zkc/Compiler/Passes.h"
#include "mlir/Pass/PassRegistry.h"
#include "zkc/Transforms/Passes.h"

namespace zkc {
void registerCompilerPasses() {
  mlir::registerPass([] { return createLowerPIRToPlanPass(); });
  mlir::registerPass([] { return createLowerPlanToPhysicalPass(); });
  mlir::registerPass([] { return createSimplifyTableRegionsPass(); });
  mlir::registerPass([] { return protocol::createExpandAlgorithmsPass(); });
  mlir::registerPass([] { return protocol::createProjectParticipantsPass(); });
  mlir::registerPass([] { return protocol::createPlanParticipantsPass(); });
  mlir::registerPass([] { return relation::createDeduplicateRelationsPass(); });
}
} // namespace zkc
