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
  if (runtime::stringifyCapabilityKind(capability.getKind()) != constructor)
    return std::nullopt;
  return llvm::SmallVector<Attribute>{
      StringAttr::get(type.getContext(), capability.getIdentity())};
}
Type constructCapability(llvm::function_ref<InFlightDiagnostic()> emit,
                         MLIRContext *context, llvm::StringRef constructor,
                         llvm::ArrayRef<Attribute> arguments) {
  auto kind = runtime::symbolizeCapabilityKind(constructor);
  return kind ? loadedCheckedType<runtime::CapabilityType>(
                    emit, context, *kind,
                    cast<StringAttr>(arguments[0]).getValue())
              : Type{};
}
Type decodeCapability(MLIRContext *context, const BoundType &type) {
  auto kind = runtime::symbolizeCapabilityKind(type.kind);
  return kind ? loadedType<runtime::CapabilityType>(context, *kind,
                                                    StringRef(type.identity))
              : Type{};
}
std::optional<BoundType> encodeCapability(Type type,
                                          llvm::StringRef constructor) {
  if (auto capability = dyn_cast<runtime::CapabilityType>(type))
    if (runtime::stringifyCapabilityKind(capability.getKind()) == constructor)
      return BoundType{constructor.str(), capability.getIdentity().str(), {}};
  return std::nullopt;
}
} // namespace
} // namespace zkc::protocol::type_adapters

#include "zkc/Dialect/TypeAdapters/Resources.inc"
