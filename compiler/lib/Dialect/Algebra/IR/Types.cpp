#include "../../DomainVerification.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Dialect/Bindings.h"
using namespace mlir;
using namespace llvm;
namespace zkc {
LogicalResult
zkc::algebra::FieldType::verify(llvm::function_ref<InFlightDiagnostic()> e,
                                StringRef d) {
  return verifyFieldDomain(e, d);
}
LogicalResult zkc::algebra::FixedVectorType::verify(
    llvm::function_ref<InFlightDiagnostic()> emit, Type element,
    uint64_t length) {
  auto logical = protocol::encodeBoundType(element, false);
  if (!logical) {
    consumeError(logical.takeError());
    return emit() << "fixed vector requires an admitted logical element type";
  }
  auto type = protocol::applyBoundType(
      "fixed_vector", {logical->spelling(), std::to_string(length)});
  if (!type) {
    consumeError(type.takeError());
    return emit() << "fixed vector exceeds logical type limits";
  }
  return success();
}
} // namespace zkc

namespace zkc::algebra {
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
  return FieldType::get(getContext(), getDomain());
}
unsigned FieldVectorType::getRank() const { return 1; }
std::optional<uint64_t> FieldVectorType::getStaticExtent(unsigned) const {
  return std::nullopt;
}

CollectionKind GroupVectorType::getCollectionKind() const {
  return CollectionKind::GroupVector;
}
Type GroupVectorType::getElementType() const {
  return GroupType::get(getContext(), getDomain());
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
  return FieldType::get(getContext(), getDomain());
}
unsigned FieldMatrixType::getRank() const { return 2; }
std::optional<uint64_t> FieldMatrixType::getStaticExtent(unsigned) const {
  return std::nullopt;
}

CollectionKind FieldArrayType::getCollectionKind() const {
  return CollectionKind::FieldArray;
}
Type FieldArrayType::getElementType() const {
  return FieldType::get(getContext(), getDomain());
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
} // namespace zkc::algebra
