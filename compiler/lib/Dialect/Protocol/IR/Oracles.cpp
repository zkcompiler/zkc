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
} // namespace zkc::protocol_ir
