#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "llvm/ADT/DenseSet.h"

using namespace mlir;
using namespace llvm;

namespace zkc {
namespace {
LogicalResult verifyPhysicalOperation(Operation *op) {
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
  if (profile.getValue() != protocol_ir::Profile::Physical)
    return diagnostics::emit(op->emitOpError(), "interactive-kernel-stage");

  return protocol::verifyBoundOperation(op, true);
}
} // namespace

bool detail::isLogicalOperationData(Type type) {
  return isa<algebra::FieldType, poly::MultilinearType, poly::QuadraticType,
             poly::PointType, algebra::GroupType, poly::UnivariateType,
             algebra::FixedVectorType, data::SequenceType, data::BytesType,
             algebra::FieldVectorType, algebra::GroupVectorType,
             algebra::IndicesType, algebra::FieldMatrixType,
             algebra::FieldArrayType, commitment::PolynomialObjectType,
             commitment::VectorObjectType, runtime::CapabilityType,
             data::VariantType, crypto::Shake128StateType,
             runtime::QuotientMatrixType>(type) ||
         type.isSignlessInteger(1) || type.isUnsignedInteger(64);
}

LogicalResult detail::verifyLogicalOperation(Operation *op) {
  // Logical primitives also appear in standard numerical functions and SCF
  // regions. Check their binding and ports here; the containing program profile
  // owns callable placement and its permitted execution vocabulary.
  return protocol::verifyBoundOperation(op, false);
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
LogicalResult zkc::plan::ApplyOp::verify() {
  return verifyPhysicalOperation(*this);
}
} // namespace zkc
