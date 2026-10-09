#include "zkc/Compiler/Passes.h"
#include "mlir/Pass/PassRegistry.h"
#include "zkc/Transforms/Passes.h"

namespace zkc {
void registerCompilerPasses() {
  mlir::registerPass([] { return protocol::createPrepareProtocolPass(); });
  mlir::registerPass([] { return protocol::createProjectProtocolPass(); });
  mlir::registerPass([] { return protocol::createLowerMathPass(); });
  mlir::registerPass([] { return protocol::createEliminatePolynomialsPass(); });
  mlir::registerPass([] { return protocol::createFixPolynomialFactorsPass(); });
  mlir::registerPass([] { return protocol::createSimplifyParticipantPass(); });
  mlir::registerPass([] { return protocol::createExpandAlgorithmsPass(); });
  mlir::registerPass([] { return protocol::createSelectPhysicalPass(); });
  mlir::registerPass([] { return relation::createDeduplicateRelationsPass(); });
}
} // namespace zkc
