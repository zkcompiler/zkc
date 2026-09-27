#include "zkc/Dialect/TypeAdapters/Support.h"
#include "zkc/Dialect/Types.h"

using namespace mlir;
namespace zkc::protocol::type_adapters {
namespace {
Type decodeCapability(MLIRContext *context, const BoundType &type) {
  return loadedType<CapabilityType>(context, type.kind + ":" + type.identity);
}
std::optional<BoundType> encodeCapability(Type type,
                                          llvm::StringRef constructor) {
  if (auto capability = dyn_cast<CapabilityType>(type)) {
    auto kind = capability.getKind();
    if (kind.consume_front(constructor) && kind.consume_front(":"))
      return BoundType{constructor.str(), kind.str(), {}};
  }
  return std::nullopt;
}
} // namespace
} // namespace zkc::protocol::type_adapters

#include "zkc/Dialect/TypeAdapters/Resources.inc"
