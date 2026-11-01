#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Residue/IR/ResidueOps.h"
#include "llvm/ADT/TypeSwitch.h"

using namespace mlir;
#include "zkc/Dialect/Residue/IR/residueDialect.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Residue/IR/residueTypes.cpp.inc"
#define GET_ATTRDEF_CLASSES
#include "zkc/Dialect/Residue/IR/residueAttrs.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Residue/IR/residueOps.cpp.inc"

namespace zkc::residue {
void ResidueDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/Residue/IR/residueTypes.cpp.inc"
      >();
  addAttributes<
#define GET_ATTRDEF_LIST
#include "zkc/Dialect/Residue/IR/residueAttrs.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Residue/IR/residueOps.cpp.inc"
      >();
}
Operation *ResidueDialect::materializeConstant(OpBuilder &builder,
                                               Attribute value, Type type,
                                               Location location) {
  auto literal = dyn_cast<LiteralAttr>(value);
  if (!literal || literal.getType() != type)
    return nullptr;
  return ResidueConstantOp::create(builder, location, type, literal);
}
LogicalResult ValueType::verify(llvm::function_ref<InFlightDiagnostic()> emit,
                                IntegerAttr modulus) {
  auto word =
      modulus ? dyn_cast<IntegerType>(modulus.getType()) : IntegerType{};
  if (!word || !word.isUnsigned() || word.getWidth() > MaximumWordWidth ||
      modulus.getValue().ult(2))
    return diagnostics::emit(
        emit(), "residue-formation",
        "modulus needs a bounded unsigned word and q >= 2");
  return success();
}
LogicalResult LiteralAttr::verify(llvm::function_ref<InFlightDiagnostic()> emit,
                                  residue::ValueType residue,
                                  IntegerAttr value) {
  if (!residue ||
      failed(residue::ValueType::verify(emit, residue.getModulus())))
    return failure();
  if (!residue || !value || value.getType() != residue.getModulus().getType() ||
      value.getValue().uge(residue.getModulus().getValue()))
    return diagnostics::emit(
        emit(), "residue-formation",
        "literal must be a canonical residue in its exact word");
  return success();
}
ValueType getElementType(Type type) {
  if (auto tensor = dyn_cast_if_present<RankedTensorType>(type)) {
    if (tensor.getEncoding())
      return {};
    type = tensor.getElementType();
  }
  return dyn_cast_if_present<ValueType>(type);
}
namespace {
LogicalResult refuse(Operation *op, llvm::StringRef message) {
  return diagnostics::emit(op->emitOpError(), "residue-formation", message);
}
IntegerType integerElement(Type type) {
  if (auto tensor = dyn_cast<RankedTensorType>(type)) {
    if (tensor.getEncoding())
      return {};
    type = tensor.getElementType();
  }
  auto word = dyn_cast<IntegerType>(type);
  return word && word.isSignless() && word.getWidth() <= MaximumWordWidth
             ? word
             : IntegerType{};
}
bool sameShape(Type left, Type right) {
  auto a = dyn_cast<RankedTensorType>(left),
       b = dyn_cast<RankedTensorType>(right);
  return bool(a) == bool(b) && (!a || a.getShape() == b.getShape());
}
LogicalResult binary(Operation *op) {
  auto type = getElementType(op->getResult(0).getType());
  if (!type)
    return refuse(op,
                  "expected canonical residue scalars or plain ranked tensors");
  return ValueType::verify([&] { return op->emitOpError(); },
                           type.getModulus());
}
LogicalResult conversion(Operation *op, bool project) {
  Type input = op->getOperand(0).getType(), output = op->getResult(0).getType();
  auto value = getElementType(project ? output : input);
  auto word = integerElement(project ? input : output);
  if (value && failed(ValueType::verify([&] { return op->emitOpError(); },
                                        value.getModulus())))
    return failure();
  if (!value || !word || !sameShape(input, output) ||
      (!project && word.getWidth() < value.getWidth()))
    return refuse(
        op, "expected equal shapes and an admitted unsigned-bit conversion");
  return success();
}
LiteralAttr literal(ValueType type, llvm::APInt value) {
  return LiteralAttr::get(type.getContext(), type,
                          IntegerAttr::get(type.getModulus().getType(), value));
}
enum class Binary { Add, Subtract, Multiply };
Attribute foldBinary(Attribute left, Attribute right, Binary kind) {
  auto a = dyn_cast_if_present<LiteralAttr>(left);
  auto b = dyn_cast_if_present<LiteralAttr>(right);
  if (!a || !b || a.getResidue() != b.getResidue())
    return {};
  auto type = a.getResidue();
  unsigned wide = 2 * type.getWidth();
  auto x = a.getValue().getValue().zext(wide);
  auto y = b.getValue().getValue().zext(wide);
  auto q = type.getModulus().getValue().zext(wide);
  llvm::APInt result = kind == Binary::Add        ? x + y
                       : kind == Binary::Subtract ? x + q - y
                                                  : x * y;
  return literal(type, result.urem(q).trunc(type.getWidth()));
}
Attribute foldLift(Attribute input, Type output, bool centered) {
  auto value = dyn_cast_if_present<LiteralAttr>(input);
  auto word = dyn_cast<IntegerType>(output);
  if (!value || !word)
    return {};
  auto result = value.getValue().getValue().zextOrTrunc(word.getWidth());
  if (centered) {
    auto q =
        value.getResidue().getModulus().getValue().zextOrTrunc(word.getWidth());
    // q/2 + q%2 avoids overflowing when q is the largest word value.
    auto threshold = q.lshr(1) + (q & 1);
    if (result.uge(threshold))
      result -= q;
  }
  return IntegerAttr::get(word, result);
}
} // namespace
LogicalResult ResidueConstantOp::verify() {
  if (getValue().getType() != getResult().getType())
    return refuse(*this, "literal and result residue identities differ");
  return LiteralAttr::verify([&] { return emitOpError(); },
                             getValue().getResidue(), getValue().getValue());
}
OpFoldResult ResidueConstantOp::fold(FoldAdaptor) { return getValue(); }
LogicalResult ResidueAddOp::verify() { return binary(*this); }
LogicalResult ResidueSubtractOp::verify() { return binary(*this); }
LogicalResult ResidueMultiplyOp::verify() { return binary(*this); }
OpFoldResult ResidueAddOp::fold(FoldAdaptor args) {
  return foldBinary(args.getLhs(), args.getRhs(), Binary::Add);
}
OpFoldResult ResidueSubtractOp::fold(FoldAdaptor args) {
  return foldBinary(args.getLhs(), args.getRhs(), Binary::Subtract);
}
OpFoldResult ResidueMultiplyOp::fold(FoldAdaptor args) {
  return foldBinary(args.getLhs(), args.getRhs(), Binary::Multiply);
}
LogicalResult ResidueProjectOp::verify() { return conversion(*this, true); }
LogicalResult ResidueLiftOp::verify() { return conversion(*this, false); }
LogicalResult ResidueCenteredLiftOp::verify() {
  return conversion(*this, false);
}
OpFoldResult ResidueProjectOp::fold(FoldAdaptor args) {
  auto input = dyn_cast_if_present<IntegerAttr>(args.getInput());
  auto value = dyn_cast<ValueType>(getResult().getType());
  if (!input || !value)
    return {};
  unsigned width = std::max(input.getValue().getBitWidth(), value.getWidth());
  return literal(value,
                 input.getValue()
                     .zextOrTrunc(width)
                     .urem(value.getModulus().getValue().zextOrTrunc(width))
                     .trunc(value.getWidth()));
}
OpFoldResult ResidueLiftOp::fold(FoldAdaptor args) {
  return foldLift(args.getInput(), getResult().getType(), false);
}
OpFoldResult ResidueCenteredLiftOp::fold(FoldAdaptor args) {
  return foldLift(args.getInput(), getResult().getType(), true);
}
} // namespace zkc::residue
