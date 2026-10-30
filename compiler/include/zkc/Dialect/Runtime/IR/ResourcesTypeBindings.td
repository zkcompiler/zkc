// Native binding decisions owned by Resource.
include "zkc/Dialect/TypeBindings.td"
def ResourceTypeAdapters : ZKC_TypeAdapterOwner<"zkc::protocol::type_adapters", "resourceAdapters">;
def RngNativeBinding : ZKC_CustomBinding<CatalogType_rng, ["::zkc::runtime::CapabilityType"], "decodeCapability", "encodeCapability", "capabilityArguments", "constructCapability", ResourceTypeAdapters>;
def NonceNativeBinding : ZKC_CustomBinding<CatalogType_nonce, ["::zkc::runtime::CapabilityType"], "decodeCapability", "encodeCapability", "capabilityArguments", "constructCapability", ResourceTypeAdapters>;
def TranscriptNativeBinding : ZKC_CustomBinding<CatalogType_transcript, ["::zkc::runtime::CapabilityType"], "decodeCapability", "encodeCapability", "capabilityArguments", "constructCapability", ResourceTypeAdapters>;
def ResourceUnitNativeBinding : ZKC_CustomBinding<CatalogType_resource_5funit, ["::zkc::runtime::CapabilityType"], "decodeCapability", "encodeCapability", "capabilityArguments", "constructCapability", ResourceTypeAdapters>;
