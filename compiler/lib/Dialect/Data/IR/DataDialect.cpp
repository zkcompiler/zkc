#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/TypeAdapters.h"
#include "zkc/Dialect/TypeFormation.h"
#include "llvm/ADT/TypeSwitch.h"
using namespace mlir;
#include "zkc/Dialect/Data/IR/dataDialect.cpp.inc"
#define GET_OP_CLASSES
#include "zkc/Dialect/Data/IR/dataOps.cpp.inc"
#define GET_TYPEDEF_CLASSES
#include "zkc/Dialect/Data/IR/dataTypes.cpp.inc"
#define GET_ATTRDEF_CLASSES
#include "zkc/Dialect/Data/IR/dataAttrs.cpp.inc"
void zkc::data::DataDialect::initialize() {
  addAttributes<
#define GET_ATTRDEF_LIST
#include "zkc/Dialect/Data/IR/dataAttrs.cpp.inc"
      >();
  addTypes<
#define GET_TYPEDEF_LIST
#include "zkc/Dialect/Data/IR/dataTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Data/IR/dataOps.cpp.inc"
      >();
  zkc::protocol::type_adapters::attachCatalogTypeModels(*this);
}
Operation *zkc::data::DataDialect::materializeConstant(OpBuilder &builder,
                                                       Attribute value,
                                                       Type type,
                                                       Location location) {
  auto integer = dyn_cast<IntegerAttr>(value);
  if (!integer || !type.isUnsignedInteger(64) || integer.getType() != type)
    return nullptr;
  return IndexOp::create(builder, location, type, integer);
}
namespace zkc::data {
CollectionKind BytesType::getCollectionKind() const {
  return CollectionKind::Bytes;
}
Type BytesType::getElementType() const {
  return IntegerType::get(getContext(), 8, IntegerType::Unsigned);
}
unsigned BytesType::getRank() const { return 1; }
std::optional<uint64_t> BytesType::getStaticExtent(unsigned) const {
  return std::nullopt;
}
CollectionKind SequenceType::getCollectionKind() const {
  return CollectionKind::Sequence;
}
unsigned SequenceType::getRank() const { return 1; }
std::optional<uint64_t> SequenceType::getStaticExtent(unsigned) const {
  return std::nullopt;
}
namespace {
LogicalResult refuse(Operation *op, StringRef reason) {
  return diagnostics::emit(op->emitOpError(), "mathematical-formation", reason);
}
} // namespace
LogicalResult SequenceType::verify(function_ref<InFlightDiagnostic()> emit,
                                   Type element) {
  if (!element)
    return emit() << "sequence requires a logical element";
  return verifyLogicalTypeApplication(emit, element.getContext(),
                                      {"sequence", {TypeAttr::get(element)}});
}
LogicalResult SequenceEmptyOp::verify() { return success(); }
LogicalResult SequenceLengthOp::verify() { return success(); }
LogicalResult SequenceAppendOp::verify() {
  if (getInput().getType() != getOutput().getType() ||
      getInput().getType().getElementType() != getElement().getType())
    return refuse(*this, "sequence element identity");
  return success();
}
OpFoldResult IndexOp::fold(FoldAdaptor) { return getValueAttr(); }
std::optional<MathematicalIdentity> IndexOp::getMathematicalIdentity() {
  return MathematicalIdentity::IndexConstant;
}
SmallVector<unsigned> IndexOp::getOperandDependencies(unsigned) { return {}; }
std::optional<MathematicalIdentity> EqualOp::getMathematicalIdentity() {
  return MathematicalIdentity::IndexEqual;
}
SmallVector<unsigned> EqualOp::getOperandDependencies(unsigned result) {
  return result == 0 ? SmallVector<unsigned>{0, 1} : SmallVector<unsigned>{};
}
std::optional<MathematicalIdentity> LessOp::getMathematicalIdentity() {
  return MathematicalIdentity::IndexLess;
}
SmallVector<unsigned> LessOp::getOperandDependencies(unsigned result) {
  return result == 0 ? SmallVector<unsigned>{0, 1} : SmallVector<unsigned>{};
}
std::optional<MathematicalIdentity> PowerOfTwoOp::getMathematicalIdentity() {
  return MathematicalIdentity::IndexPowerOfTwo;
}
SmallVector<unsigned> PowerOfTwoOp::getOperandDependencies(unsigned result) {
  return result == 0 ? SmallVector<unsigned>{0, 1} : SmallVector<unsigned>{};
}
LogicalResult PowerOfTwoOp::verify() { return success(); }
std::optional<MathematicalIdentity>
IndexWrappingAddOp::getMathematicalIdentity() {
  return MathematicalIdentity::IndexWrappingAdd;
}
SmallVector<unsigned>
IndexWrappingAddOp::getOperandDependencies(unsigned result) {
  return result == 0 ? SmallVector<unsigned>{0, 1} : SmallVector<unsigned>{};
}
std::optional<MathematicalIdentity>
IndexWrappingSubtractOp::getMathematicalIdentity() {
  return MathematicalIdentity::IndexWrappingSubtract;
}
SmallVector<unsigned>
IndexWrappingSubtractOp::getOperandDependencies(unsigned result) {
  return result == 0 ? SmallVector<unsigned>{0, 1} : SmallVector<unsigned>{};
}
std::optional<MathematicalIdentity> IndexBitAndOp::getMathematicalIdentity() {
  return MathematicalIdentity::IndexBitAnd;
}
SmallVector<unsigned> IndexBitAndOp::getOperandDependencies(unsigned result) {
  return result == 0 ? SmallVector<unsigned>{0, 1} : SmallVector<unsigned>{};
}
std::optional<MathematicalIdentity>
IndexLogicalShiftRightOp::getMathematicalIdentity() {
  return MathematicalIdentity::IndexLogicalShiftRight;
}
SmallVector<unsigned>
IndexLogicalShiftRightOp::getOperandDependencies(unsigned result) {
  return result == 0 ? SmallVector<unsigned>{0, 1} : SmallVector<unsigned>{};
}
std::optional<MathematicalIdentity> DimOp::getMathematicalIdentity() {
  if (getAxis() == 0 && isa<algebra::FieldVectorType>(getInput().getType()))
    return MathematicalIdentity::VectorLength;
  return std::nullopt;
}
SmallVector<unsigned> DimOp::getOperandDependencies(unsigned result) {
  return result == 0 ? SmallVector<unsigned>{0} : SmallVector<unsigned>{};
}
LogicalResult EqualOp::verify() { return success(); }
LogicalResult LessOp::verify() { return success(); }
LogicalResult MakeOp::verify() {
  auto alternatives = getOutput().getType().getAlternatives();
  auto arm = llvm::find_if(alternatives, [&](auto arm) {
    return arm.getLabel().getValue() == getAlternative();
  });
  if (arm == alternatives.end() ||
      TypeRange(arm->getPayload()) != getOperandTypes())
    return refuse(*this, "aggregate alternative or payload identity");
  return success();
}
LogicalResult GetOp::verify() {
  auto alternatives = getInput().getType().getAlternatives();
  auto index = getIndexAttr().getInt();
  if (alternatives.size() != 1 || index < 0 ||
      uint64_t(index) >= alternatives.front().getPayload().size())
    return refuse(
        *this, "total projection requires one alternative and a valid field");
  if (getOutput().getType() != alternatives.front().getPayload()[index])
    return refuse(*this, "aggregate field identity");
  return success();
}
LogicalResult IsOp::verify() {
  if (!llvm::any_of(getInput().getType().getAlternatives(), [&](auto arm) {
        return arm.getLabel().getValue() == getAlternative();
      }))
    return refuse(*this, "unknown aggregate alternative");
  return success();
}
LogicalResult DimOp::verify() {
  auto collection = cast<CollectionTypeInterface>(getInput().getType());
  auto axis = getAxisAttr().getInt();
  if (axis < 0 || uint64_t(axis) >= collection.getRank())
    return refuse(*this, "collection dimension axis");
  return success();
}
} // namespace zkc::data
