#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "llvm/ADT/StringSet.h"
using namespace mlir;
namespace zkc::protocol_ir {
LogicalResult OracleSendOp::verify() {
  auto kind = getHandle().getType().getKind();
  if (!kind.getDataType() || getData().getType() != kind.getDataType())
    return emitOpError("data must match its oracle kind");
  llvm::StringSet<> receivers;
  if (getSender().empty() || getReceivers().empty())
    return emitOpError("requires a sender and nonempty receivers");
  for (auto role : getReceivers()) {
    auto name = cast<StringAttr>(role).getValue();
    if (name.empty() || name == getSender() || !receivers.insert(name).second)
      return emitOpError(
          "requires distinct nonempty receivers other than the sender");
  }
  auto dimensions = kind.getShapeDimensions();
  if (getShape().size() != dimensions.size() ||
      getShapeNames().size() != dimensions.size())
    return emitOpError("shape operands must match every named kind dimension");
  for (auto [name, dimension] : llvm::zip(getShapeNames(), dimensions))
    if (cast<StringAttr>(name).getValue() != dimension.name)
      return emitOpError(
          "shape names must follow the kind's exact dimension order");
  return kind.verifyShapeBounds([&] { return emitOpError(); },
                                getShapeBounds());
}
Value OracleSendOp::getShapeOperand(llvm::StringRef name) {
  for (auto [dimension, value] : llvm::zip(getShapeNames(), getShape()))
    if (cast<StringAttr>(dimension).getValue() == name)
      return value;
  return {};
}
LogicalResult OracleQueryOp::verify() {
  bool declaration = isa<OracleDefinitionOp>((*this)->getParentOp());
  if (declaration ? bool(getOwnerAttr()) : !getOwnerAttr())
    return emitOpError(
        "owner is implicit only inside a virtual query declaration");
  auto kind = getHandle().getType().getKind();
  if (!kind.getQueryType() || getPosition().getType() != kind.getQueryType() ||
      getAnswer().getType() != kind.getAnswerType())
    return emitOpError("position and answer must match the oracle kind");
  return success();
}
LogicalResult OracleForgetShapeOp::verify() {
  auto from = getInput().getType().getKind(),
       to = getOutput().getType().getKind();
  auto before = from.getShapeDimensions(), after = to.getShapeDimensions();
  if (from.getIdentity() != to.getIdentity() ||
      from.getDataType() != to.getDataType() ||
      from.getQueryType() != to.getQueryType() ||
      from.getAnswerType() != to.getAnswerType() ||
      before.size() != after.size())
    return emitOpError(
        "shape erasure must preserve the oracle kind and associations");
  bool erased = false;
  for (auto [source, target] : llvm::zip(before, after)) {
    if (source.name != target.name ||
        (target.extent && target.extent != source.extent))
      return emitOpError("shape erasure cannot add or change an extent");
    erased |= source.extent.has_value() && !target.extent;
  }
  return erased ? success()
                : emitOpError(
                      "shape erasure must forget at least one static extent");
}
LogicalResult OracleShapeOp::verify() {
  for (const auto &dimension :
       getHandle().getType().getKind().getShapeDimensions())
    if (dimension.name == getDimension())
      return success();
  return emitOpError("shape read must name a dimension of the oracle kind");
}
LogicalResult OracleContentsOp::verify() {
  if (getData().getType() != getHandle().getType().getKind().getDataType())
    return emitOpError("contents must have the oracle kind's data type");
  return success();
}
LogicalResult OracleSequenceAppendOp::verify() {
  auto type = getPrefix().getType();
  if (getOutput().getType() != type ||
      getElement().getType().getKind() != type.getKind())
    return emitOpError("append must preserve the sequence bound and kind");
  return success();
}
LogicalResult OracleSequenceAtOp::verify() {
  if (getHandle().getType().getKind() != getSequence().getType().getKind())
    return emitOpError("selection must preserve the actual handle kind");
  return success();
}
LogicalResult OracleInputOp::verify() {
  auto kind = getHandle().getType().getKind();
  if (getAnchor().getType() != getHandle().getType() ||
      getData().getType() != kind.getDataType())
    return emitOpError("input components must preserve the kind and data type");
  return kind.verifyShapeBounds([&] { return emitOpError(); },
                                getShapeBounds());
}
LogicalResult OracleComponentsOp::verify() {
  if (getAnchor().getType() != getHandle().getType() ||
      getData().getType() != getHandle().getType().getKind().getDataType())
    return emitOpError("components must preserve the kind and data type");
  return success();
}
} // namespace zkc::protocol_ir
