#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Dialect/TypeAdapters/Support.h"
#include "zkc/Dialect/Types.h"

using namespace mlir;
namespace zkc::protocol::type_adapters {
namespace {
using FieldAdapter = DomainAdapter<zkc::algebra::FieldType>;
Type decodeMatrix(MLIRContext *context, const BoundType &type) {
  auto field = loadedType<algebra::FieldType>(context, type.identity);
  return field ? RankedTensorType::get(
                     {ShapedType::kDynamic, ShapedType::kDynamic}, field)
               : Type{};
}
std::optional<BoundType> encodeMatrix(Type type, llvm::StringRef constructor) {
  auto tensor = dyn_cast<RankedTensorType>(type);
  if (!tensor || tensor.getRank() != 2 || !tensor.isDynamicDim(0) ||
      !tensor.isDynamicDim(1) || tensor.getEncoding())
    return std::nullopt;
  return encodeDomainType<algebra::FieldType>(tensor.getElementType(),
                                              constructor);
}
using FixedVectorAdapter =
    TypeNatAdapter<zkc::algebra::FixedVectorType,
                   &zkc::algebra::FixedVectorType::getElementType,
                   &zkc::algebra::FixedVectorType::getLength>;
Type decodeFieldArray(MLIRContext *context, const BoundType &type) {
  if (!type.identity.empty() || type.arguments.size() != 2 ||
      type.arguments[0].kind != TypeArgument::Kind::Domain ||
      type.arguments[1].kind != TypeArgument::Kind::Nat ||
      type.arguments[1].natural > algebra::MaximumArrayLength)
    return {};
  auto element =
      loadedType<algebra::FieldType>(context, type.arguments[0].domain);
  return element ? RankedTensorType::get({int64_t(type.arguments[1].natural)},
                                         element)
                 : Type{};
}
std::optional<BoundType> encodeFieldArray(Type type,
                                          llvm::StringRef constructor) {
  if (!algebra::isFieldArray(type))
    return std::nullopt;
  auto array = cast<RankedTensorType>(type);
  auto field = cast<algebra::FieldType>(array.getElementType());
  return BoundType{constructor.str(),
                   {},
                   {},
                   {TypeArgument::domainArgument(field.getDomain().str()),
                    TypeArgument::naturalArgument(array.getDimSize(0))}};
}
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
