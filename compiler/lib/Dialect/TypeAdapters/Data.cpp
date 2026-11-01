#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/TypeAdapters/Support.h"
#include "zkc/Dialect/Types.h"
using namespace mlir;
namespace zkc::protocol::type_adapters {
namespace {
std::optional<llvm::SmallVector<Attribute>> sequenceArguments(Type type,
                                                              llvm::StringRef) {
  auto sequence = dyn_cast<zkc::data::SequenceType>(type);
  if (!sequence || !sequence.getElementType())
    return std::nullopt;
  return llvm::SmallVector<Attribute>{TypeAttr::get(sequence.getElementType())};
}
Type constructSequence(llvm::function_ref<InFlightDiagnostic()> emit,
                       MLIRContext *context, llvm::StringRef,
                       llvm::ArrayRef<Attribute> arguments) {
  return loadedCheckedType<zkc::data::SequenceType>(
      emit, context, cast<TypeAttr>(arguments[0]).getValue());
}
Type decodeSequence(MLIRContext *context, const BoundType &type) {
  if (type.arguments.size() != 1 ||
      type.arguments[0].kind != TypeArgument::Kind::Type)
    return {};
  auto element = decodeBoundType(context, *type.arguments[0].type);
  return element ? loadedType<zkc::data::SequenceType>(context, element)
                 : Type{};
}
std::optional<BoundType> encodeSequence(Type type,
                                        llvm::StringRef constructor) {
  auto sequence = dyn_cast<zkc::data::SequenceType>(type);
  if (!sequence)
    return std::nullopt;
  auto element = encodeBoundType(sequence.getElementType(), false);
  if (!element) {
    llvm::consumeError(element.takeError());
    return std::nullopt;
  }
  return BoundType{constructor.str(),
                   {},
                   {},
                   {TypeArgument::typeArgument(std::move(*element))}};
}
Type decodeVariantType(MLIRContext *context, const BoundType &type) {
  auto registered =
      context ? AbstractType::lookup(zkc::data::VariantType::name, context)
              : std::nullopt;
  if (!registered ||
      registered->get().getTypeID() != zkc::data::VariantType::getTypeID())
    return {};
  auto descriptor = decodeVariant("variant:" + type.identity);
  return descriptor ? zkc::data::importVariantType(context, *descriptor)
                    : Type{};
}
std::optional<BoundType> encodeVariantType(Type type,
                                           llvm::StringRef constructor) {
  // This required contribution callback shares the canonical structural codec.
  // It owns neither a second table encoder nor native admission semantics.
  if (!isa<zkc::data::VariantType>(type) || constructor != "variant")
    return std::nullopt;
  auto result = encodeBoundType(type, false);
  if (result)
    return std::move(*result);
  llvm::consumeError(result.takeError());
  return std::nullopt;
}
using BytesAdapter = NullaryAdapter<zkc::data::BytesType>;

using FieldVectorAdapter = DomainAdapter<zkc::data::FieldVectorType>;
using FieldMatrixAdapter = DomainAdapter<zkc::data::FieldMatrixType>;
using IndicesAdapter = NullaryAdapter<zkc::data::IndicesType>;
using FieldArrayAdapter =
    DomainNatAdapter<zkc::data::FieldArrayType,
                     &zkc::data::FieldArrayType::getDomain,
                     &zkc::data::FieldArrayType::getLength>;
using FixedVectorAdapter =
    TypeNatAdapter<zkc::data::FixedVectorType,
                   &zkc::data::FixedVectorType::getElementType,
                   &zkc::data::FixedVectorType::getLength>;
using GroupVectorAdapter = DomainAdapter<zkc::data::GroupVectorType>;
} // namespace
} // namespace zkc::protocol::type_adapters
#include "zkc/Dialect/TypeAdapters/Data.inc"
