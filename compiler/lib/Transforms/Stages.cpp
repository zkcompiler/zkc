#include "zkc/Transforms/Stages.h"
#include "mlir/Pass/PassManager.h"

namespace zkc {
void buildPreparationPipeline(mlir::OpPassManager &pm, bool simplify,
                              MathematicalSelectionPolicy policy,
                              mathematical::RealizationTrace *trace) {
  pm.addPass(protocol::createPrepareProtocolPass(simplify, policy, trace));
}
void buildProjectionPipeline(mlir::OpPassManager &pm, bool simplify,
                             MathematicalSelectionPolicy policy) {
  pm.addPass(protocol::createProjectProtocolPass(simplify, policy));
}
void buildExecutionPipeline(mlir::OpPassManager &pm, bool simplify,
                            bool fixPolynomials,
                            MathematicalSelectionPolicy policy,
                            mathematical::RealizationTrace *trace) {
  if (simplify)
    pm.addPass(protocol::createSimplifyParticipantPass());
  if (fixPolynomials)
    pm.addPass(protocol::createFixPolynomialFactorsPass());
  pm.addPass(protocol::createLowerMathPass(policy, trace));
}
void buildClosedExecutionPipeline(mlir::OpPassManager &pm, bool simplify,
                                  bool fixPolynomials,
                                  MathematicalSelectionPolicy policy,
                                  mathematical::RealizationTrace *trace) {
  if (simplify)
    pm.addPass(protocol::createSimplifyParticipantPass());
  if (fixPolynomials)
    pm.addPass(protocol::createFixPolynomialFactorsPass());
  pm.addPass(protocol::createLowerClosedParticipantPass(policy, trace));
}
} // namespace zkc
