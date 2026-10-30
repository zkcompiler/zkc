#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Transforms/Passes.h"

using namespace mlir;
namespace zkc {
namespace {
struct AdmitStagePass : PassWrapper<AdmitStagePass, OperationPass<>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(AdmitStagePass)
  StringRef getArgument() const final { return "zkc-admit-stage"; }
  StringRef getDescription() const final {
    return "Admit the complete native stage without changing IR";
  }
  bool canScheduleOn(RegisteredOperationName name) const final {
    return name.getStringRef() == ModuleOp::getOperationName() ||
           name.getStringRef() ==
               protocol_ir::ProtocolModuleOp::getOperationName();
  }
  void runOnOperation() final {
    if (failed(admitStage(getOperation())))
      return signalPassFailure();
    markAllAnalysesPreserved();
  }
};
} // namespace
std::unique_ptr<Pass> createAdmitStagePass() {
  return std::make_unique<AdmitStagePass>();
}
} // namespace zkc
