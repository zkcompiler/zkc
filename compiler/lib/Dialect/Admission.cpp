#include "zkc/Dialect/Admission.h"
#include "Verification.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"

using namespace mlir;
namespace zkc {
namespace {
bool boundedStructure(Operation *owner) {
  unsigned remaining = 1000000;
  SmallVector<std::pair<Operation *, unsigned>> pending{{owner, 0}};
  while (!pending.empty()) {
    auto [operation, depth] = pending.pop_back_val();
    if (!remaining || depth > 128)
      return false;
    --remaining;
    for (auto &region : operation->getRegions())
      for (auto &block : region)
        for (auto &child : block) {
          if (pending.size() >= remaining)
            return false;
          pending.emplace_back(&child, depth + 1);
        }
  }
  return true;
}
} // namespace
LogicalResult admitStage(Operation *owner) {
  if (!owner)
    return failure();
  if (!isa<ModuleOp, protocol_ir::ProtocolModuleOp>(owner))
    return diagnostics::emit(owner->emitOpError(), "stage-admission-owner",
                             "admission requires the complete symbol owner");
  if (!boundedStructure(owner))
    return diagnostics::emit(emitError(owner->getLoc()),
                             "stage-admission-limit",
                             "native structure exceeds depth or work limits");
  if (failed(verify(owner)))
    return failure();
  auto result = owner->walk([&](Operation *operation) {
    if (auto computation = dyn_cast<ModuleOp>(operation)) {
      if ((computation->hasAttr("exec.computation") ||
           isa_and_nonnull<protocol_ir::ProtocolModuleOp>(
               computation->getParentOp())) &&
          failed(mathematical::verifyComputationUnit(computation)))
        return WalkResult::interrupt();
      return WalkResult::advance();
    }
    auto unit = dyn_cast<protocol_ir::ProtocolModuleOp>(operation);
    if (!unit)
      return WalkResult::advance();
    if (protocol_ir::isMathematicalProfile(unit.getProfile()))
      return failed(mathematical::verifyModule(unit)) ? WalkResult::interrupt()
                                                      : WalkResult::advance();
    mathematical::NativeTypePolicies types(unit);
    if (failed(mathematical::verifyProjectionMetadata(unit, types)) ||
        failed(mathematical::verifyNativeExecution(unit, types)) ||
        failed(protocol::verifyModule(unit)))
      return WalkResult::interrupt();
    return WalkResult::advance();
  });
  return failure(result.wasInterrupted());
}
} // namespace zkc
