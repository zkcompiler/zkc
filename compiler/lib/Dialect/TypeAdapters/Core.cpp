#include "zkc/Dialect/TypeAdapters/Support.h"
#include "zkc/Dialect/Types.h"

using namespace mlir;
namespace zkc::protocol::type_adapters {
namespace {
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
  return loadedType<VariantType>(context, "variant:" + type.identity);
}
std::optional<BoundType> encodeVariantType(Type type,
                                           llvm::StringRef constructor) {
  if (auto variant = dyn_cast<VariantType>(type)) {
    auto descriptor = variant.getDescriptor();
    if (descriptor.consume_front("variant:"))
      return BoundType{constructor.str(), descriptor.str(), {}};
  }
  return std::nullopt;
}
} // namespace
} // namespace zkc::protocol::type_adapters

#include "zkc/Dialect/TypeAdapters/Core.inc"
