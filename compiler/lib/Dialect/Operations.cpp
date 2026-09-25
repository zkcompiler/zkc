#include "Verification.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Plan/IR/Physical.h"
#include "zkc/Interfaces/SourceLibrary.h"
#include "zkc/Translation/Protocol.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
using namespace llvm;
#include "zkc/Interfaces/SourceOpInterface.cpp.inc"

namespace zkc {
static LogicalResult field(llvm::function_ref<InFlightDiagnostic()> emit,
                           StringRef d) {
  if (d != "f2" && d != "f7" && d != "reference.scalar" &&
      protocol::installedDomains().identitySort(d) != "Field")
    return diagnostics::emit(emit(), "unknown-domain");
  return success();
}
static bool digits(StringRef n) {
  return !n.empty() && n.size() <= 1024 &&
         (n.size() == 1 || n.front() != '0') &&
         llvm::all_of(n, [](char c) { return c >= '0' && c <= '9'; });
}
LogicalResult FieldType::verify(llvm::function_ref<InFlightDiagnostic()> e,
                                StringRef d) {
  return field(e, d);
}
LogicalResult ScalarType::verify(llvm::function_ref<InFlightDiagnostic()> e,
                                 StringRef d) {
  return field(e, d);
}
LogicalResult PrepareOp::verify() {
  return verifyPhysicalOperationContext(*this);
}
LogicalResult InvokeOp::verify() {
  return verifyPhysicalOperationContext(*this);
}
LogicalResult PointType::verify(llvm::function_ref<InFlightDiagnostic()> e,
                                StringRef d) {
  return field(e, d);
}
LogicalResult TableType::verify(llvm::function_ref<InFlightDiagnostic()> e,
                                StringRef d, StringRef n) {
  if (failed(field(e, d)))
    return failure();
  if (!digits(n))
    return diagnostics::emit(e(), "invalid-original-rank");
  return success();
}
LogicalResult ResidualType::verify(llvm::function_ref<InFlightDiagnostic()> e,
                                   StringRef d, StringRef n) {
  return TableType::verify(e, d, n);
}
json::Value ViewOp::getSourceDescriptor() {
  auto t = cast<TableType>(getOrigin().getType());
  return json::Array{"view", t.getDomain(), naturalValue(t.getRank())};
}
json::Value RestrictOp::getSourceDescriptor() {
  auto t = cast<ResidualType>(getView().getType());
  return json::Array{"restrict", t.getDomain(), naturalValue(t.getRank())};
}
json::Value EvaluateOp::getSourceDescriptor() {
  auto t = cast<ResidualType>(getView().getType());
  return json::Array{"evaluate", t.getDomain(), naturalValue(t.getRank())};
}
json::Value AddOp::getSourceDescriptor() {
  return json::Array{"add", cast<FieldType>(getLhs().getType()).getDomain()};
}
json::Value RecordOp::getSourceDescriptor() {
  return json::Array{"record",
                     cast<FieldType>(getInput().getType()).getDomain()};
}
json::Value AbortWriteOp::getSourceDescriptor() {
  return json::Array{"abort_write",
                     cast<FieldType>(getInput().getType()).getDomain()};
}
json::Value EndpointPointOp::getSourceDescriptor() {
  return json::Array{"endpoint_point", getAtOne()};
}
json::Value ParentOp::getSourceDescriptor() {
  return json::Array{"parent", getLeft()};
}
#define DESCRIPTOR(CLASS, NAME)                                                \
  json::Value CLASS::getSourceDescriptor() { return json::Array{NAME}; }
DESCRIPTOR(OrderedPairOp, "ordered_pair")
DESCRIPTOR(PackOp, "pack")
DESCRIPTOR(SendOp, "send")
DESCRIPTOR(DrawOp, "draw")
DESCRIPTOR(LinearOp, "linear")
DESCRIPTOR(PointOp, "point")
DESCRIPTOR(EqualOp, "equal")
DESCRIPTOR(DigestEqualOp, "digest_equal")
#undef DESCRIPTOR
LogicalResult ViewOp::verify() { return verifySourceOperationContext(*this); }
LogicalResult RestrictOp::verify() {
  return verifySourceOperationContext(*this);
}
LogicalResult EvaluateOp::verify() {
  return verifySourceOperationContext(*this);
}
LogicalResult AddOp::verify() { return verifySourceOperationContext(*this); }
LogicalResult RecordOp::verify() { return verifySourceOperationContext(*this); }
LogicalResult AbortWriteOp::verify() {
  return verifySourceOperationContext(*this);
}
LogicalResult OrderedPairOp::verify() {
  return verifySourceOperationContext(*this);
}
LogicalResult PackOp::verify() { return verifySourceOperationContext(*this); }
LogicalResult SendOp::verify() { return verifySourceOperationContext(*this); }
LogicalResult DrawOp::verify() { return verifySourceOperationContext(*this); }
LogicalResult LinearOp::verify() { return verifySourceOperationContext(*this); }
LogicalResult PointOp::verify() { return verifySourceOperationContext(*this); }
LogicalResult EndpointPointOp::verify() {
  return verifySourceOperationContext(*this);
}
LogicalResult EqualOp::verify() { return verifySourceOperationContext(*this); }
LogicalResult ParentOp::verify() { return verifySourceOperationContext(*this); }
LogicalResult DigestEqualOp::verify() {
  return verifySourceOperationContext(*this);
}
LogicalResult PIRProgramOp::verifyRegions() { return verifyProgram(*this); }
LogicalResult PlanProgramOp::verifyRegions() { return verifyProgram(*this); }
static LogicalResult stop(Operation *op, StringRef reason) {
  if (reason != "reject" && reason != "abort" && reason != "exhausted" &&
      reason != "incomplete" && reason != "refused")
    return diagnostics::emit(op->emitOpError(), "unknown-stop");
  return success();
}
LogicalResult PIRStopOp::verify() { return stop(*this, getReason()); }
LogicalResult PlanStopOp::verify() { return stop(*this, getReason()); }
} // namespace zkc

mlir::LogicalResult zkc::ProtocolModuleOp::verifyRegions() {
  return protocol::verifyModule(*this);
}
