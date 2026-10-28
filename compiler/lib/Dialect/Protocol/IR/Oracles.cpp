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
  auto maximum = getMaximumRowsAttr();
  if (kind.getStaticRows()) {
    if (maximum)
      return emitOpError("a sized kind already determines its row maximum");
  } else if (!maximum || !maximum.getType().isUnsignedInteger(64))
    return emitOpError("a runtime row count requires a ui64 maximum_rows");
  return success();
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
LogicalResult OracleForgetRowsOp::verify() {
  auto from = getInput().getType().getKind(),
       to = getOutput().getType().getKind();
  if (!from.getStaticRows() || to.getStaticRows() ||
      from.getIdentity() != to.getIdentity() ||
      from.getAnswerType() != to.getAnswerType() || !to.getDataType())
    return emitOpError("may only forget an exact row count of the same kind");
  return success();
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
  if (kind.getStaticRows() ? bool(getMaximumRowsAttr()) : !getMaximumRowsAttr())
    return emitOpError("only an unsized input requires maximum_rows");
  return success();
}
LogicalResult OracleComponentsOp::verify() {
  if (getAnchor().getType() != getHandle().getType() ||
      getData().getType() != getHandle().getType().getKind().getDataType())
    return emitOpError("components must preserve the kind and data type");
  return success();
}
} // namespace zkc::protocol_ir
