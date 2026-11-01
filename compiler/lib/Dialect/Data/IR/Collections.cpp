#include "zkc/Dialect/Data/Collections.h"
#include "../../DomainVerification.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/TypeFormation.h"
using namespace mlir;
using namespace llvm;
namespace zkc::data {
LogicalResult
FixedVectorType::verify(llvm::function_ref<InFlightDiagnostic()> emit,
                        Type element, uint64_t length) {
  if (!element || length > MaximumArrayLength)
    return emit()
           << "fixed vector requires a logical element and bounded length";
  auto *context = element.getContext();
  return verifyLogicalTypeApplication(
      emit, context,
      {"fixed_vector",
       {TypeAttr::get(element),
        IntegerAttr::get(IntegerType::get(context, 64, IntegerType::Unsigned),
                         length)}});
}

LogicalResult
FieldVectorType::verify(llvm::function_ref<InFlightDiagnostic()> emit,
                        StringRef domain) {
  return verifyFieldDomain(emit, domain);
}
LogicalResult
FieldMatrixType::verify(llvm::function_ref<InFlightDiagnostic()> emit,
                        StringRef domain) {
  return verifyFieldDomain(emit, domain);
}
LogicalResult
FieldArrayType::verify(llvm::function_ref<InFlightDiagnostic()> emit,
                       StringRef domain, uint64_t length) {
  if (failed(verifyFieldDomain(emit, domain)))
    return failure();
  if (length > MaximumArrayLength)
    return emit() << "field array exceeds logical length limit";
  return success();
}

CollectionKind FieldVectorType::getCollectionKind() const {
  return CollectionKind::FieldVector;
}
Type FieldVectorType::getElementType() const {
  return algebra::FieldType::get(getContext(), getDomain());
}
unsigned FieldVectorType::getRank() const { return 1; }
std::optional<uint64_t> FieldVectorType::getStaticExtent(unsigned) const {
  return std::nullopt;
}

CollectionKind GroupVectorType::getCollectionKind() const {
  return CollectionKind::GroupVector;
}
Type GroupVectorType::getElementType() const {
  return algebra::GroupType::get(getContext(), getDomain());
}
unsigned GroupVectorType::getRank() const { return 1; }
std::optional<uint64_t> GroupVectorType::getStaticExtent(unsigned) const {
  return std::nullopt;
}

CollectionKind IndicesType::getCollectionKind() const {
  return CollectionKind::Indices;
}
Type IndicesType::getElementType() const {
  return IntegerType::get(getContext(), 64, IntegerType::Unsigned);
}
unsigned IndicesType::getRank() const { return 1; }
std::optional<uint64_t> IndicesType::getStaticExtent(unsigned) const {
  return std::nullopt;
}

CollectionKind FieldMatrixType::getCollectionKind() const {
  return CollectionKind::FieldMatrix;
}
Type FieldMatrixType::getElementType() const {
  return algebra::FieldType::get(getContext(), getDomain());
}
unsigned FieldMatrixType::getRank() const { return 2; }
std::optional<uint64_t> FieldMatrixType::getStaticExtent(unsigned) const {
  return std::nullopt;
}

CollectionKind FieldArrayType::getCollectionKind() const {
  return CollectionKind::FieldArray;
}
Type FieldArrayType::getElementType() const {
  return algebra::FieldType::get(getContext(), getDomain());
}
unsigned FieldArrayType::getRank() const { return 1; }
std::optional<uint64_t> FieldArrayType::getStaticExtent(unsigned axis) const {
  return axis == 0 ? std::optional<uint64_t>(getLength()) : std::nullopt;
}

CollectionKind FixedVectorType::getCollectionKind() const {
  return CollectionKind::FixedVector;
}
unsigned FixedVectorType::getRank() const { return 1; }
std::optional<uint64_t> FixedVectorType::getStaticExtent(unsigned axis) const {
  return axis == 0 ? std::optional<uint64_t>(getLength()) : std::nullopt;
}
namespace {
LogicalResult refuse(Operation *op, llvm::StringRef reason) {
  return diagnostics::emit(op->emitOpError(), "mathematical-formation", reason);
}
} // namespace
bool isFieldArray(Type type) {
  auto array = dyn_cast_if_present<data::FieldArrayType>(type);
  if (!array || array.getLength() > MaximumArrayLength)
    return false;
  return protocol::installedDomains().identitySort(array.getDomain()) ==
         "Field";
}
LogicalResult ArrayFromElementsOp::verify() {
  auto type = getResult().getType();
  if (!isFieldArray(type) || getElements().size() != type.getLength() ||
      !llvm::all_of(getOperandTypes(), [&](Type element) {
        return element == type.getElementType();
      }))
    return refuse(*this, "expected exact field-array length and element field");
  return success();
}
LogicalResult ArrayAtOp::verify() {
  auto type = getArray().getType();
  auto index = getIndexAttr().getInt();
  if (!isFieldArray(type) || index < 0 || uint64_t(index) >= type.getLength() ||
      type.getElementType() != getResult().getType())
    return diagnostics::emit(
        emitOpError(), "mathematical-formation",
        "expected static in-bounds field-array extraction");
  return success();
}
OpFoldResult ArrayAtOp::fold(FoldAdaptor) {
  if (auto packed = getArray().getDefiningOp<ArrayFromElementsOp>())
    return packed.getElements()[getIndexAttr().getInt()];
  return {};
}
std::optional<MathematicalIdentity> ArrayAtOp::getMathematicalIdentity() {
  return MathematicalIdentity::ArrayAt;
}
std::optional<MathematicalIdentity>
ArrayFromElementsOp::getMathematicalIdentity() {
  return MathematicalIdentity::ArrayFromElements;
}
SmallVector<unsigned>
ArrayFromElementsOp::getOperandDependencies(unsigned result) {
  SmallVector<unsigned> dependencies;
  if (result == 0)
    for (unsigned i = 0; i < getNumOperands(); ++i)
      dependencies.push_back(i);
  return dependencies;
}
SmallVector<unsigned> ArrayAtOp::getOperandDependencies(unsigned result) {
  return result == 0 ? SmallVector<unsigned>{0} : SmallVector<unsigned>{};
}
} // namespace zkc::data
