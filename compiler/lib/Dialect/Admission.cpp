#include "zkc/Dialect/Admission.h"
#include "AdmissionPrivate.h"
#include "NativeTypeWork.h"
#include "Verification.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "llvm/ADT/ScopeExit.h"

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
LogicalResult
detail::verifyStageStructure(Operation *owner,
                             protocol::SourceExecutionClosure *sourceClosure) {
  if (!owner)
    return failure();
  if (!isa<ModuleOp, protocol_ir::ProtocolModuleOp>(owner))
    return diagnostics::emit(owner->emitOpError(), "stage-admission-owner",
                             "admission requires the complete symbol owner");
  // Native accounting callbacks and their immutable caches are scoped to this
  // thread. MLIR otherwise dispatches isolated operation verifiers to workers.
  // Admission owns synchronous access to this context for this call.
  auto *context = owner->getContext();
  bool serial = detail::NativeTypeWorkScope::current() &&
                context->isMultithreadingEnabled();
  if (serial)
    context->disableMultithreading();
  auto restoreThreading = llvm::scope_exit([&] {
    if (serial)
      context->enableMultithreading();
  });
  if (!boundedStructure(owner))
    return diagnostics::emit(emitError(owner->getLoc()),
                             "stage-admission-limit",
                             "native structure exceeds depth or work limits");
  if (failed(verify(owner)))
    return failure();
  auto outer = dyn_cast<protocol_ir::ProtocolModuleOp>(owner);
  if (auto module = dyn_cast<ModuleOp>(owner))
    if (hasSingleElement(module.getBody()->getOperations()))
      outer =
          dyn_cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
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
      return failed(detail::verifyMathematicalStructure(
                 unit, unit == outer ? sourceClosure : nullptr))
                 ? WalkResult::interrupt()
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
LogicalResult
detail::admitStageWithWork(Operation *owner, facts::Work &work,
                           protocol::SourceExecutionClosure *sourceClosure) {
  // Refuse before even the structural verifier if a previous phase exhausted
  // this allowance. A fresh admission must never restart its derivation.
  if (!work.charge(0))
    return failure();
  if (failed(detail::verifyStageStructure(owner, sourceClosure)))
    return failure();
  auto result = owner->walk([&](protocol_ir::ProtocolModuleOp unit) {
    if (unit.getProfile() != protocol_ir::Profile::Protocol)
      return WalkResult::advance();
    auto requirements = detail::completeCommonControl(unit, work);
    if (!requirements) {
      diagnostics::emit(unit.emitOpError(), requirements.takeError());
      return WalkResult::interrupt();
    }
    return WalkResult::advance();
  });
  return failure(result.wasInterrupted());
}
LogicalResult admitStage(Operation *owner) {
  uint64_t remaining = 1000000;
  facts::Work work(remaining);
  return detail::admitStageWithWork(owner, work);
}
} // namespace zkc
