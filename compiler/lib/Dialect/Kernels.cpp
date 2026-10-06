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
  auto module = op->getParentOfType<zkc::protocol_ir::ProtocolModuleOp>();
  auto *owner = op->getParentOp();
  while (owner && isa<zkc::local::LocalIfOp, zkc::local::LocalForOp,
                      zkc::local::LocalMatchOp>(owner))
    owner = owner->getParentOp();
  if (!module || !isa_and_nonnull<zkc::local::FuncOp>(owner))
    return diagnostics::emit(op->emitOpError(), "interactive-kernel-context",
                             "expected a local function in protocol.module");
  auto profile = module.getProfileAttr();
  if (!profile)
    return diagnostics::emit(op->emitOpError(), "interactive-kernel-context",
                             "missing profile");
  if (physical ? profile.getValue() != protocol_ir::Profile::Physical
               : profile.getValue() == protocol_ir::Profile::Physical)
    return diagnostics::emit(op->emitOpError(), "interactive-kernel-stage");

  return protocol::verifyBoundOperation(op, physical);
}
} // namespace

bool detail::isLogicalKernelData(Type type) {
  return isa<algebra::FieldType, poly::MultilinearType, poly::QuadraticType,
             poly::PointType, algebra::GroupType, poly::UnivariateType,
             algebra::FixedVectorType, data::SequenceType, RankedTensorType,
             pcs::ObjectType, oracle::OracleObjectType, local::CapabilityType,
             local::VariantType>(type) ||
         type.isSignlessInteger(1) || type.isUnsignedInteger(64);
}

LogicalResult detail::verifyLogicalKernel(Operation *op) {
  return verifyKernel(op, false);
}

LogicalResult zkc::plan::ReleaseOp::verify() {
  auto root = (*this)->getParentOfType<zkc::protocol_ir::ProtocolModuleOp>();
  auto *owner = (*this)->getParentOp();
  while (owner && isa<zkc::local::LocalIfOp, zkc::local::LocalForOp,
                      zkc::local::LocalMatchOp>(owner))
    owner = owner->getParentOp();
  auto function = dyn_cast_or_null<zkc::local::FuncOp>(owner);
  if (!root || root.getProfile() != zkc::protocol_ir::Profile::Physical ||
      !function || !llvm::hasSingleElement(function.getBody()))
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
LogicalResult zkc::plan::ExecuteKernelOp::verify() {
  return verifyKernel(*this, true);
}
} // namespace zkc
