#include "zkc/Dialect/TypeAdapters/Support.h"
#include "zkc/Dialect/Types.h"

using namespace mlir;
namespace zkc::protocol::type_adapters {
namespace {
std::optional<llvm::SmallVector<Attribute>>
capabilityArguments(Type type, llvm::StringRef constructor) {
  auto capability = dyn_cast<zkc::runtime::CapabilityType>(type);
  if (!capability)
    return std::nullopt;
  auto identity = capability.getKind();
  if (!identity.consume_front(constructor) || !identity.consume_front(":"))
    return std::nullopt;
  return llvm::SmallVector<Attribute>{
      StringAttr::get(type.getContext(), identity)};
}
Type constructCapability(llvm::function_ref<InFlightDiagnostic()> emit,
                         MLIRContext *context, llvm::StringRef constructor,
                         llvm::ArrayRef<Attribute> arguments) {
  return loadedCheckedType<zkc::runtime::CapabilityType>(
      emit, context,
      (constructor + ":" + cast<StringAttr>(arguments[0]).getValue()).str());
}
Type decodeCapability(MLIRContext *context, const BoundType &type) {
  return loadedType<zkc::runtime::CapabilityType>(context, type.kind + ":" +
                                                               type.identity);
}
std::optional<BoundType> encodeCapability(Type type,
                                          llvm::StringRef constructor) {
  if (auto capability = dyn_cast<zkc::runtime::CapabilityType>(type)) {
    auto kind = capability.getKind();
    if (kind.consume_front(constructor) && kind.consume_front(":"))
      return BoundType{constructor.str(), kind.str(), {}};
  }
  return std::nullopt;
}
} // namespace
} // namespace zkc::protocol::type_adapters

#include "zkc/Dialect/TypeAdapters/Resources.inc"
