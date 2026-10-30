// Native binding decisions owned by Core.
include "zkc/Dialect/TypeBindings.td"
def CoreTypeAdapters : ZKC_TypeAdapterOwner<"zkc::protocol::type_adapters", "coreAdapters">;
def SequenceNativeBinding : ZKC_CustomBinding<CatalogType_sequence, ["::zkc::data::SequenceType"], "decodeSequence", "encodeSequence", "sequenceArguments", "constructSequence", CoreTypeAdapters>;
def Shake128NativeBinding : ZKC_DirectBinding<CatalogType_shake128_5fstate, Shake128State, "Shake128Adapter", CoreTypeAdapters>;
def BytesNativeBinding : ZKC_DirectBinding<CatalogType_bytes, Bytes, "BytesAdapter", CoreTypeAdapters>;
def BoolNativeBinding : ZKC_CustomBinding<CatalogType_bool, ["::mlir::IntegerType"], "decodeBoolean", "encodeBoolean", "booleanArguments", "constructBoolean", CoreTypeAdapters>;
def IndexNativeBinding : ZKC_CustomBinding<CatalogType_index, ["::mlir::IntegerType"], "decodeIndex", "encodeIndex", "indexArguments", "constructIndex", CoreTypeAdapters>;
def VariantNativeBinding : ZKC_SpecialBinding<VariantSyntax, ["::zkc::data::VariantType"], "decodeVariantType", "encodeVariantType", CoreTypeAdapters>;
