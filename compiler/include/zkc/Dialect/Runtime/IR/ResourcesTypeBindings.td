// Native binding decisions owned by Resource.
include "zkc/Dialect/TypeBindings.td"
def ResourceTypeAdapters : ZKC_TypeAdapterOwner<"zkc::protocol::type_adapters", "resourceAdapters">;
def RngNativeBinding : ZKC_CustomBinding<TypeRng, ["::zkc::runtime::CapabilityType"], "decodeCapability", "encodeCapability", ResourceTypeAdapters>;
def NonceNativeBinding : ZKC_CustomBinding<TypeNonce, ["::zkc::runtime::CapabilityType"], "decodeCapability", "encodeCapability", ResourceTypeAdapters>;
def TranscriptNativeBinding : ZKC_CustomBinding<TypeTranscript, ["::zkc::runtime::CapabilityType"], "decodeCapability", "encodeCapability", ResourceTypeAdapters>;
def ResourceUnitNativeBinding : ZKC_CustomBinding<TypeResourceUnit, ["::zkc::runtime::CapabilityType"], "decodeCapability", "encodeCapability", ResourceTypeAdapters>;
