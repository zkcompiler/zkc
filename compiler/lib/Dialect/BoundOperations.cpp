#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/IR.h"

using namespace mlir;
using namespace llvm;

namespace zkc {
bool detail::isLogicalOperationData(Type type) {
  return isa<algebra::FieldType, poly::MultilinearType, poly::QuadraticType,
             poly::PointType, algebra::GroupType, poly::UnivariateType,
             algebra::FixedVectorType, data::SequenceType, data::BytesType,
             algebra::FieldVectorType, algebra::GroupVectorType,
             algebra::IndicesType, algebra::FieldMatrixType,
             algebra::FieldArrayType, commitment::PolynomialObjectType,
             commitment::VectorObjectType, runtime::CapabilityType,
             data::VariantType, crypto::Shake128StateType,
             runtime::QuotientMatrixType>(type) ||
         type.isSignlessInteger(1) || type.isUnsignedInteger(64);
}

LogicalResult detail::verifyLogicalOperation(Operation *op) {
  // Logical primitives also appear in standard numerical functions and SCF
  // regions. Check their binding and ports here; the containing program profile
  // owns callable placement and its permitted execution vocabulary.
  return protocol::verifyBoundOperation(op);
}

} // namespace zkc
