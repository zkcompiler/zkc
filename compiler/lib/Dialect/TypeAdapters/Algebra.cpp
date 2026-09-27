#include "zkc/Dialect/TypeAdapters/Support.h"
#include "zkc/Dialect/Types.h"

using namespace mlir;
namespace zkc::protocol::type_adapters {
namespace {
using FieldAdapter = DomainAdapter<FieldType>;
using MatrixAdapter = DomainAdapter<MatrixType>;
using FixedVectorAdapter =
    TypeNatAdapter<FixedVectorType, &FixedVectorType::getElementType,
                   &FixedVectorType::getLength>;
Type decodeIndices(MLIRContext *context, const BoundType &) {
  return vectorType(IntegerType::get(context, 64, IntegerType::Unsigned));
}
std::optional<BoundType> encodeIndices(Type type, llvm::StringRef constructor) {
  auto element = vectorElement(type);
  if (element && element.isUnsignedInteger(64))
    return BoundType{constructor.str(), {}, {}};
  return std::nullopt;
}
} // namespace
} // namespace zkc::protocol::type_adapters

#include "zkc/Dialect/TypeAdapters/Algebra.inc"
