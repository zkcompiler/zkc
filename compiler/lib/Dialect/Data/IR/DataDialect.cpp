#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Diagnostics.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/Data/IR/dataDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Data/IR/dataOps.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Data/IR/dataTypes.cpp.inc"
void zkc::data::DataDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/Data/IR/dataTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Data/IR/dataOps.cpp.inc"
      >();
}
namespace zkc::data {
namespace {
LogicalResult refuse(Operation *op, StringRef reason) {
  return diagnostics::emit(op->emitOpError(), "mathematical-formation", reason);
}
} // namespace
LogicalResult SequenceType::verify(function_ref<InFlightDiagnostic()> emit,
                                   Type element) {
  auto bound = protocol::encodeBoundType(element, false);
  if (!bound) {
    llvm::consumeError(bound.takeError());
    return emit() << "sequence element must have a canonical logical type";
  }
  if (!protocol::duplicable(*bound) || !protocol::discardable(*bound))
    return emit() << "sequence element must be copyable and discardable";
  protocol::BoundType sequence{
      "sequence", {}, {}, {protocol::TypeArgument::typeArgument(*bound)}};
  auto formed = protocol::parseBoundType(sequence.spelling(), false);
  if (!formed)
    return emit() << llvm::toString(formed.takeError());
  if (protocol::decodeBoundType(element.getContext(), *bound) != element)
    return emit() << "sequence element must use its canonical MLIR type";
  return success();
}
LogicalResult SequenceEmptyOp::verify() { return success(); }
LogicalResult SequenceLengthOp::verify() { return success(); }
LogicalResult SequenceAppendOp::verify() {
  if (getInput().getType() != getOutput().getType() ||
      getInput().getType().getElementType() != getElement().getType())
    return refuse(*this, "sequence element identity");
  return success();
}
LogicalResult IndexOp::verify() {
  uint64_t value;
  auto text = getValue();
  if (text.empty() || (text.size() > 1 && text.front() == '0') ||
      !llvm::all_of(text, [](char c) { return c >= '0' && c <= '9'; }) ||
      text.getAsInteger(10, value))
    return refuse(*this, "expected a canonical unsigned 64-bit natural");
  return success();
}
LogicalResult EqualOp::verify() { return success(); }
LogicalResult LessOp::verify() { return success(); }
LogicalResult MakeOp::verify() {
  auto descriptor =
      protocol::decodeVariant(getOutput().getType().getDescriptor());
  if (!descriptor)
    return refuse(*this, "invalid aggregate descriptor");
  auto arm = llvm::find_if(descriptor->alternatives, [&](const auto &arm) {
    return arm.label == getAlternative();
  });
  if (arm == descriptor->alternatives.end() ||
      arm->payload.size() != getPayload().size())
    return refuse(*this, "aggregate alternative or payload arity");
  for (auto [type, spelling] : llvm::zip(getOperandTypes(), arm->payload)) {
    auto actual = protocol::encodeBoundType(type, false);
    if (!actual) {
      llvm::consumeError(actual.takeError());
      return refuse(*this, "aggregate payload type");
    }
    if (actual->spelling() != spelling)
      return refuse(*this, "aggregate payload identity");
  }
  return success();
}
LogicalResult GetOp::verify() {
  auto descriptor =
      protocol::decodeVariant(getInput().getType().getDescriptor());
  auto index = getIndexAttr().getInt();
  if (!descriptor || descriptor->alternatives.size() != 1 || index < 0 ||
      uint64_t(index) >= descriptor->alternatives.front().payload.size())
    return refuse(
        *this, "total projection requires one alternative and a valid field");
  auto actual = protocol::encodeBoundType(getOutput().getType(), false);
  if (!actual) {
    llvm::consumeError(actual.takeError());
    return refuse(*this, "aggregate result type");
  }
  if (actual->spelling() != descriptor->alternatives.front().payload[index])
    return refuse(*this, "aggregate field identity");
  return success();
}
LogicalResult IsOp::verify() {
  auto descriptor =
      protocol::decodeVariant(getInput().getType().getDescriptor());
  if (!descriptor ||
      !llvm::any_of(descriptor->alternatives, [&](const auto &arm) {
        return arm.label == getAlternative();
      }))
    return refuse(*this, "unknown aggregate alternative");
  return success();
}
LogicalResult DimOp::verify() {
  auto tensor = getInput().getType();
  auto axis = getAxisAttr().getInt();
  if (axis < 0 || axis >= tensor.getRank())
    return refuse(*this, "tensor dimension axis");
  auto bound = protocol::encodeBoundType(tensor, false);
  if (!bound) {
    llvm::consumeError(bound.takeError());
    return refuse(*this, "unsupported canonical tensor");
  }
  if (bound->kind != "vector" && bound->kind != "matrix" &&
      bound->kind != "indices" && bound->kind != "groups" &&
      bound->kind != "field_array")
    return refuse(*this, "unsupported tensor shape observation");
  return success();
}
} // namespace zkc::data
