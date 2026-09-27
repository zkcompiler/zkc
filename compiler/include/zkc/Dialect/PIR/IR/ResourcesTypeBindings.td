// Native binding decisions owned by Resource.
include "zkc/Dialect/TypeBindings.td"
def ResourceTypeAdapters : ZKC_TypeAdapterOwner<"zkc::protocol::type_adapters", "resourceAdapters">;
def RngNativeBinding : ZKC_CustomBinding<TypeRng, ["::zkc::CapabilityType"], "decodeCapability", "encodeCapability", ResourceTypeAdapters>;
def NonceNativeBinding : ZKC_CustomBinding<TypeNonce, ["::zkc::CapabilityType"], "decodeCapability", "encodeCapability", ResourceTypeAdapters>;
def TranscriptNativeBinding : ZKC_CustomBinding<TypeTranscript, ["::zkc::CapabilityType"], "decodeCapability", "encodeCapability", ResourceTypeAdapters>;
def ResourceUnitNativeBinding : ZKC_CustomBinding<TypeResourceUnit, ["::zkc::CapabilityType"], "decodeCapability", "encodeCapability", ResourceTypeAdapters>;
