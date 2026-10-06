#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Dialect/Plan/IR/PlanTypes.h"
#include "zkc/Support/Json.h"
using namespace mlir;
using namespace llvm;

namespace zkc {
namespace {
LogicalResult localControlContext(Operation *op) {
  auto *owner = op->getParentOp();
  while (owner && isa<zkc::local::LocalIfOp, zkc::local::LocalForOp,
                      zkc::local::LocalMatchOp>(owner))
    owner = owner->getParentOp();
  if (!isa_and_nonnull<zkc::local::FuncOp>(owner))
    return diagnostics::emit(op->emitOpError(), "local-control-context");
  return success();
}
Type localLogical(Type type) {
  if (auto physical = dyn_cast<zkc::plan::DataType>(type))
    return physical.getLogical();
  return type;
}
LogicalResult localRegion(Operation *op, Region &region, TypeRange inputs,
                          TypeRange outputs, unsigned forwarded = 0) {
  if (!llvm::hasSingleElement(region) || region.front().empty() ||
      region.front().getArgumentTypes() != inputs)
    return diagnostics::emit(op->emitOpError(), "local-control-arguments");
  auto &block = region.front();
  auto *end = &block.back();
  if (isa<zkc::local::StopOp>(end))
    return success();
  bool conditional = isa<zkc::local::LocalConditionOp>(end);
  unsigned offset = conditional ? 1 : 0;
  if (conditional &&
      (!isa<zkc::local::LocalForOp>(op) || !end->getNumOperands() ||
       !localLogical(end->getOperand(0).getType()).isSignlessInteger(1)))
    return diagnostics::emit(op->emitOpError(), "local-if-condition");
  if ((!conditional && !isa<zkc::local::LocalYieldOp>(end)) ||
      end->getNumOperands() != offset + outputs.size() + forwarded ||
      end->getOperands()
              .drop_front(offset)
              .take_front(outputs.size())
              .getTypes() != outputs)
    return diagnostics::emit(op->emitOpError(), "local-control-yield");
  for (unsigned i = 0; i < forwarded; ++i)
    if (end->getOperand(offset + outputs.size() + i) !=
        block.getArgument(block.getNumArguments() - forwarded + i))
      return diagnostics::emit(op->emitOpError(),
                               "local-control-capture-forwarding");
  return success();
}
// Both construction and matching materialize the same flattened payload.
Expected<SmallVector<Type>> variantPayloadTypes(ArrayRef<std::string> payload,
                                                bool physical,
                                                MLIRContext *context) {
  SmallVector<Type> types;
  for (const auto &leaf : payload) {
    auto parsed = protocol::parseBoundType(leaf, false);
    if (!parsed) {
      consumeError(parsed.takeError());
      return zkc::error("variant-type");
    }
    if (physical) {
      parsed = protocol::defaultRepresentation(*parsed);
      if (!parsed) {
        consumeError(parsed.takeError());
        return zkc::error("binding-representation");
      }
    }
    auto type = protocol::decodeBoundType(context, *parsed);
    if (!type)
      return zkc::error("variant-type");
    types.push_back(type);
  }
  return types;
}
} // namespace
LogicalResult zkc::local::VariantInjectOp::verify() {
  if (failed(localControlContext(*this)))
    return failure();
  auto bound = protocol::encodeBoundType(
      getOutput().getType(), isa<zkc::plan::DataType>(getOutput().getType()));
  if (!bound) {
    consumeError(bound.takeError());
    return diagnostics::emit(emitOpError(), "variant-type");
  }
  auto descriptor = protocol::decodeVariant("variant:" + bound->identity);
  if (bound->kind != "variant" || !descriptor)
    return diagnostics::emit(emitOpError(), "variant-type");
  auto arm = llvm::find_if(descriptor->alternatives, [&](const auto &a) {
    return a.label == getAlternative();
  });
  if (arm == descriptor->alternatives.end())
    return diagnostics::emit(emitOpError(), "variant-alternative");
  auto expected = variantPayloadTypes(
      arm->payload, !bound->representation.empty(), getContext());
  if (!expected)
    return diagnostics::emit(emitOpError(), expected.takeError());
  if (getOperandTypes() != TypeRange(*expected))
    return diagnostics::emit(emitOpError(), "variant-payload");
  return success();
}
LogicalResult zkc::local::LocalMatchOp::verifyRegions() {
  if (failed(localControlContext(*this)))
    return failure();
  if (getNumOperands() < 1)
    return diagnostics::emit(emitOpError(), "variant-type");
  bool physical = isa<zkc::plan::DataType>(getOperand(0).getType());
  auto bound = protocol::encodeBoundType(getOperand(0).getType(), physical);
  if (!bound) {
    consumeError(bound.takeError());
    return diagnostics::emit(emitOpError(), "variant-type");
  }
  auto descriptor = protocol::decodeVariant(
      bound->spelling().substr(0, bound->spelling().find('@')));
  if (!descriptor)
    return diagnostics::emit(emitOpError(), "variant-type");
  if (getNumRegions() != descriptor->alternatives.size() ||
      getAlternatives().size() != getNumRegions())
    return diagnostics::emit(emitOpError(), "local-match-arms");
  for (auto [i, arm] : llvm::enumerate(descriptor->alternatives)) {
    auto label = dyn_cast<StringAttr>(getAlternatives()[i]);
    if (!label || label.getValue() != arm.label)
      return diagnostics::emit(emitOpError(), "local-match-arm");
    auto inputs = variantPayloadTypes(arm.payload, physical, getContext());
    if (!inputs)
      return diagnostics::emit(emitOpError(), inputs.takeError());
    llvm::append_range(*inputs, getOperands().drop_front().getTypes());
    if (failed(localRegion(*this, getRegion(i), *inputs, getResultTypes())))
      return failure();
  }
  return success();
}
OperandRange
zkc::local::LocalMatchOp::getEntrySuccessorOperands(RegionSuccessor) {
  return getOperands().drop_front(std::min(1u, getNumOperands()));
}
ValueRange
zkc::local::LocalMatchOp::getSuccessorInputs(RegionSuccessor successor) {
  if (successor.isOperation())
    return getResults();
  auto *region = successor.getSuccessor();
  if (!region || region->empty())
    return {};
  auto args = region->front().getArguments();
  unsigned captures = getNumOperands() ? getNumOperands() - 1 : 0;
  return args.take_back(std::min<size_t>(captures, args.size()));
}
void zkc::local::LocalMatchOp::getSuccessorRegions(
    RegionBranchPoint point, SmallVectorImpl<RegionSuccessor> &regions) {
  if (point.isParent()) {
    for (auto &region : getArms())
      regions.emplace_back(&region);
  } else {
    auto end = point.getTerminatorPredecessorOrNull();
    if (end && isa<zkc::local::LocalYieldOp>(end.getOperation()))
      regions.emplace_back(getOperation());
  }
}
LogicalResult zkc::local::LocalIfOp::verifyRegions() {
  if (failed(localControlContext(*this)))
    return failure();
  if (getNumOperands() < 1 ||
      !localLogical(getOperand(0).getType()).isSignlessInteger(1))
    return diagnostics::emit(emitOpError(), "local-if-condition");
  auto inputs = getOperands().drop_front().getTypes();
  if (failed(localRegion(*this, getThenRegion(), inputs, getResultTypes())) ||
      failed(localRegion(*this, getElseRegion(), inputs, getResultTypes())))
    return failure();
  return success();
}
LogicalResult zkc::local::LocalForOp::verifyRegions() {
  if (failed(localControlContext(*this)))
    return failure();
  unsigned n = getNumResults();
  if (getNumOperands() < n + 2 ||
      !localLogical(getOperand(0).getType()).isUnsignedInteger(64) ||
      getOperand(0).getType() != getOperand(1).getType() ||
      getOperands().slice(2, n).getTypes() != getResultTypes())
    return diagnostics::emit(emitOpError(), "local-for-bounds");
  SmallVector<Type> inputs{getOperand(0).getType()};
  llvm::append_range(inputs, getOperands().drop_front(2).getTypes());
  return localRegion(*this, getBody(), inputs, getResultTypes(),
                     getNumOperands() - n - 2);
}
OperandRange zkc::local::LocalIfOp::getEntrySuccessorOperands(RegionSuccessor) {
  return getOperands().drop_front(std::min(1u, getNumOperands()));
}
ValueRange
zkc::local::LocalIfOp::getSuccessorInputs(RegionSuccessor successor) {
  if (successor.isOperation())
    return getResults();
  auto *region = successor.getSuccessor();
  return region && !region->empty() ? ValueRange(region->front().getArguments())
                                    : ValueRange{};
}
void zkc::local::LocalIfOp::getSuccessorRegions(
    RegionBranchPoint point, SmallVectorImpl<RegionSuccessor> &regions) {
  if (point.isParent()) {
    regions.emplace_back(&getThenRegion());
    regions.emplace_back(&getElseRegion());
  } else
    regions.emplace_back(getOperation());
}
OperandRange
zkc::local::LocalForOp::getEntrySuccessorOperands(RegionSuccessor successor) {
  auto inputs = getOperands().drop_front(std::min(2u, getNumOperands()));
  return successor.isOperation() ? inputs.take_front(std::min<unsigned>(
                                       getNumResults(), inputs.size()))
                                 : inputs;
}
ValueRange
zkc::local::LocalForOp::getSuccessorInputs(RegionSuccessor successor) {
  if (successor.isOperation())
    return getResults();
  // The induction value is generated by the bounded loop, not forwarded.
  if (getBody().empty())
    return {};
  auto arguments = getBody().front().getArguments();
  return arguments.drop_front(std::min<size_t>(1, arguments.size()));
}
void zkc::local::LocalForOp::getSuccessorRegions(
    RegionBranchPoint, SmallVectorImpl<RegionSuccessor> &regions) {
  regions.emplace_back(&getBody());
  regions.emplace_back(getOperation());
}
MutableOperandRange zkc::local::LocalYieldOp::getMutableSuccessorOperands(
    RegionSuccessor successor) {
  if (successor.isOperation())
    return MutableOperandRange(
        getOperation(), 0,
        std::min((*this)->getParentOp()->getNumResults(), getNumOperands()));
  return MutableOperandRange(getOperation());
}
MutableOperandRange zkc::local::LocalConditionOp::getMutableSuccessorOperands(
    RegionSuccessor successor) {
  // Region-interface verification precedes the parent's shape verifier. Keep
  // malformed short tuples bounded so the interface can report a type error.
  auto inputs = getInputsMutable();
  return successor.isOperation()
             ? inputs.slice(
                   0, std::min(getOperation()->getParentOp()->getNumResults(),
                               inputs.size()))
             : inputs;
}
} // namespace zkc
