// Native binding decisions owned by Core.
include "zkc/Dialect/TypeBindings.td"
def CoreTypeAdapters : ZKC_TypeAdapterOwner<"zkc::protocol::type_adapters", "coreAdapters">;
def BoolNativeBinding : ZKC_CustomBinding<TypeBool, ["::mlir::IntegerType"], "decodeBoolean", "encodeBoolean", CoreTypeAdapters>;
def IndexNativeBinding : ZKC_CustomBinding<TypeIndex, ["::mlir::IntegerType"], "decodeIndex", "encodeIndex", CoreTypeAdapters>;
def VariantNativeBinding : ZKC_SpecialBinding<VariantSyntax, ["::zkc::VariantType"], "decodeVariantType", "encodeVariantType", CoreTypeAdapters>;
def ScalarNativeBinding : ZKC_UnavailableBinding<TypeScalar, "Physical scalar carrier is not a logical binding">;
def CapabilityNativeBinding : ZKC_UnavailableBinding<TypeCapability, "Capability is a native container, not an admitted logical constructor">;
