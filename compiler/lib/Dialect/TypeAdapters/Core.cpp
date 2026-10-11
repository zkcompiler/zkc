#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/TypeAdapters/Support.h"
#include "zkc/Dialect/Types.h"

using namespace mlir;
namespace zkc::protocol::type_adapters {
namespace {
Type decodeShake128(MLIRContext *context, const BoundType &) {
  return loadedType<zkc::crypto::Shake128StateType>(context);
}
std::optional<BoundType> encodeShake128(Type type,
                                        llvm::StringRef constructor) {
  if (isa<zkc::crypto::Shake128StateType>(type))
    return BoundType{constructor.str(), {}, {}};
  return std::nullopt;
}
Type decodeBytes(MLIRContext *context, const BoundType &) {
  return vectorType(IntegerType::get(context, 8, IntegerType::Unsigned));
}
std::optional<BoundType> encodeBytes(Type type, llvm::StringRef constructor) {
  auto element = vectorElement(type);
  if (element && element.isUnsignedInteger(8))
    return BoundType{constructor.str(), {}, {}};
  return std::nullopt;
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
  auto element = encodeLogicalType(sequence.getElementType());
  if (!element) {
    llvm::consumeError(element.takeError());
    return std::nullopt;
  }
  return BoundType{constructor.str(),
                   {},
                   {},
                   {TypeArgument::typeArgument(std::move(*element))}};
}
Type decodeBoolean(MLIRContext *context, const BoundType &) {
  return IntegerType::get(context, 1);
}
std::optional<BoundType> encodeBoolean(Type type, llvm::StringRef constructor) {
  if (type.isSignlessInteger(1))
    return BoundType{constructor.str(), {}, {}};
  return std::nullopt;
}
Type decodeIndex(MLIRContext *context, const BoundType &) {
  return IntegerType::get(context, 64, IntegerType::Unsigned);
}
std::optional<BoundType> encodeIndex(Type type, llvm::StringRef constructor) {
  if (type.isUnsignedInteger(64))
    return BoundType{constructor.str(), {}, {}};
  return std::nullopt;
}
Type decodeVariantType(MLIRContext *context, const BoundType &type) {
  return loadedType<zkc::local::VariantType>(context,
                                             "variant:" + type.identity);
}
std::optional<BoundType> encodeVariantType(Type type,
                                           llvm::StringRef constructor) {
  if (auto variant = dyn_cast<zkc::local::VariantType>(type)) {
    auto descriptor = variant.getDescriptor();
    if (descriptor.consume_front("variant:"))
      return BoundType{constructor.str(), descriptor.str(), {}};
  }
  return std::nullopt;
}
} // namespace
} // namespace zkc::protocol::type_adapters

#include "zkc/Dialect/TypeAdapters/Core.inc"
