#include "../../DomainVerification.h"
#include "../../Verification.h"
#include "zkc/Dialect/Table/IR/Physical.h"
#include "zkc/Dialect/Table/IR/TableOps.h"
#include "zkc/Interfaces/SourceLibrary.h"
using namespace mlir;
using namespace llvm;
namespace zkc {
LogicalResult
zkc::table::ScalarType::verify(llvm::function_ref<InFlightDiagnostic()> e,
                               StringRef d) {
  return verifyFieldDomain(e, d);
}
LogicalResult zkc::table::PrepareOp::verify() {
  return verifyPhysicalOperationContext(*this);
}
LogicalResult zkc::table::InvokeOp::verify() {
  return verifyPhysicalOperationContext(*this);
}
json::Value zkc::table::ViewOp::getSourceDescriptor() {
  auto t = cast<zkc::poly::TableType>(getOrigin().getType());
  return json::Array{"view", t.getDomain(), naturalValue(t.getRank())};
}
json::Value zkc::table::RestrictOp::getSourceDescriptor() {
  auto t = cast<zkc::poly::ResidualType>(getView().getType());
  return json::Array{"restrict", t.getDomain(), naturalValue(t.getRank())};
}
json::Value zkc::table::EvaluateOp::getSourceDescriptor() {
  auto t = cast<zkc::poly::ResidualType>(getView().getType());
  return json::Array{"evaluate", t.getDomain(), naturalValue(t.getRank())};
}
json::Value zkc::table::AddOp::getSourceDescriptor() {
  return json::Array{
      "add", cast<zkc::algebra::FieldType>(getLhs().getType()).getDomain()};
}
json::Value zkc::table::RecordOp::getSourceDescriptor() {
  return json::Array{
      "record",
      cast<zkc::algebra::FieldType>(getInput().getType()).getDomain()};
}
json::Value zkc::table::AbortWriteOp::getSourceDescriptor() {
  return json::Array{
      "abort_write",
      cast<zkc::algebra::FieldType>(getInput().getType()).getDomain()};
}
json::Value zkc::table::EndpointPointOp::getSourceDescriptor() {
  return json::Array{"endpoint_point", getAtOne()};
}
json::Value zkc::table::ParentOp::getSourceDescriptor() {
  return json::Array{"parent", getLeft()};
}
#define DESCRIPTOR(CLASS, NAME)                                                \
  json::Value CLASS::getSourceDescriptor() { return json::Array{NAME}; }
DESCRIPTOR(zkc::table::OrderedPairOp, "ordered_pair")
DESCRIPTOR(zkc::table::PackOp, "pack")
DESCRIPTOR(zkc::table::SendOp, "send")
DESCRIPTOR(zkc::table::DrawOp, "draw")
DESCRIPTOR(zkc::table::LinearOp, "linear")
DESCRIPTOR(zkc::table::PointOp, "point")
DESCRIPTOR(zkc::table::EqualOp, "equal")
DESCRIPTOR(zkc::table::DigestEqualOp, "digest_equal")
#undef DESCRIPTOR
LogicalResult zkc::table::ViewOp::verify() {
  return verifySourceOperationContext(*this);
}
LogicalResult zkc::table::RestrictOp::verify() {
  return verifySourceOperationContext(*this);
}
LogicalResult zkc::table::EvaluateOp::verify() {
  return verifySourceOperationContext(*this);
}
LogicalResult zkc::table::AddOp::verify() {
  return verifySourceOperationContext(*this);
}
LogicalResult zkc::table::RecordOp::verify() {
  return verifySourceOperationContext(*this);
}
LogicalResult zkc::table::AbortWriteOp::verify() {
  return verifySourceOperationContext(*this);
}
LogicalResult zkc::table::OrderedPairOp::verify() {
  return verifySourceOperationContext(*this);
}
LogicalResult zkc::table::PackOp::verify() {
  return verifySourceOperationContext(*this);
}
LogicalResult zkc::table::SendOp::verify() {
  return verifySourceOperationContext(*this);
}
LogicalResult zkc::table::DrawOp::verify() {
  return verifySourceOperationContext(*this);
}
LogicalResult zkc::table::LinearOp::verify() {
  return verifySourceOperationContext(*this);
}
LogicalResult zkc::table::PointOp::verify() {
  return verifySourceOperationContext(*this);
}
LogicalResult zkc::table::EndpointPointOp::verify() {
  return verifySourceOperationContext(*this);
}
LogicalResult zkc::table::EqualOp::verify() {
  return verifySourceOperationContext(*this);
}
LogicalResult zkc::table::ParentOp::verify() {
  return verifySourceOperationContext(*this);
}
LogicalResult zkc::table::DigestEqualOp::verify() {
  return verifySourceOperationContext(*this);
}
LogicalResult zkc::table::PIRProgramOp::verifyRegions() {
  return verifyProgram(*this);
}
LogicalResult zkc::table::PlanProgramOp::verifyRegions() {
  return verifyProgram(*this);
}
static LogicalResult stop(Operation *op, StringRef reason) {
  if (reason != "reject" && reason != "abort" && reason != "exhausted" &&
      reason != "incomplete" && reason != "refused")
    return diagnostics::emit(op->emitOpError(), "unknown-stop");
  return success();
}
LogicalResult zkc::table::PIRStopOp::verify() {
  return stop(*this, getReason());
}
LogicalResult zkc::table::PlanStopOp::verify() {
  return stop(*this, getReason());
}
} // namespace zkc
