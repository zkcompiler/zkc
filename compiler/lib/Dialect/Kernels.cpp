#include "zkc/Contracts/Kernels.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "llvm/ADT/DenseSet.h"

using namespace mlir;
using namespace llvm;

namespace zkc {
namespace {
LogicalResult verifyKernel(Operation *op, bool physical) {
  auto module = op->getParentOfType<ProtocolModuleOp>();
  auto *owner = op->getParentOp();
  while (owner && isa<LocalIfOp, LocalForOp, LocalMatchOp>(owner))
    owner = owner->getParentOp();
  if (!module || (!isa_and_nonnull<func::FuncOp>(owner) &&
                  (physical || !isa_and_nonnull<PureRegionOp>(owner))))
    return diagnostics::emit(
        op->emitOpError(), "interactive-kernel-context",
        "expected a local function or logical pure region in pir.module");
  auto stage = module.getStageAttr();
  if (!stage)
    return diagnostics::emit(op->emitOpError(), "interactive-kernel-context",
                             "missing stage");
  if (physical ? stage.getValue() != "physical"
               : stage.getValue() != "common" && stage.getValue() != "logical")
    return diagnostics::emit(op->emitOpError(), "interactive-kernel-stage");

  return protocol::verifyBoundOperation(op, physical);
}
} // namespace

LogicalResult detail::verifyLogicalKernel(Operation *op) {
  return verifyKernel(op, false);
}

LogicalResult ReleaseOp::verify() {
  auto root = (*this)->getParentOfType<ProtocolModuleOp>();
  auto *owner = (*this)->getParentOp();
  while (owner && isa<LocalIfOp, LocalForOp, LocalMatchOp>(owner))
    owner = owner->getParentOp();
  auto function = dyn_cast_or_null<func::FuncOp>(owner);
  if (!root || root.getStage() != "physical" || !function ||
      !llvm::hasSingleElement(function.getBody()))
    return diagnostics::emit(emitOpError(), "interactive-release-context");
  if (getValues().empty())
    return diagnostics::emit(emitOpError(), "interactive-release-empty");
  llvm::DenseSet<Value> seen;
  for (auto value : getValues()) {
    if (!seen.insert(value).second)
      return diagnostics::emit(emitOpError(),
                               "interactive-release-unavailable");
    auto type = protocol::encodeBoundType(value.getType(), true);
    if (!type)
      return diagnostics::emit(emitOpError(), type.takeError());
    bool canDiscard = protocol::discardable(type->spelling());
    if (!canDiscard)
      return diagnostics::emit(emitOpError(), "interactive-release-resource");
    for (auto &use : value.getUses()) {
      auto *owner = use.getOwner();
      if (owner == getOperation())
        continue;
      if (owner->getBlock() != (*this)->getBlock() ||
          !owner->isBeforeInBlock(getOperation()))
        return diagnostics::emit(emitOpError(), "interactive-release-live");
    }
  }
  return success();
}
LogicalResult ExecuteKernelOp::verify() { return verifyKernel(*this, true); }
} // namespace zkc
