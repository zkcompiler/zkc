// Native binding decisions owned by Core.
include "zkc/Dialect/TypeBindings.td"
def CoreTypeAdapters : ZKC_TypeAdapterOwner<"zkc::protocol::type_adapters", "coreAdapters">;
def SequenceNativeBinding : ZKC_CustomBinding<TypeSequence, ["::zkc::data::SequenceType"], "decodeSequence", "encodeSequence", CoreTypeAdapters>;
def Shake128NativeBinding : ZKC_DirectBinding<TypeShake128State, Shake128State, "Shake128Adapter", CoreTypeAdapters>;
def BytesNativeBinding : ZKC_DirectBinding<TypeBytes, Bytes, "BytesAdapter", CoreTypeAdapters>;
def BoolNativeBinding : ZKC_CustomBinding<TypeBool, ["::mlir::IntegerType"], "decodeBoolean", "encodeBoolean", CoreTypeAdapters>;
def IndexNativeBinding : ZKC_CustomBinding<TypeIndex, ["::mlir::IntegerType"], "decodeIndex", "encodeIndex", CoreTypeAdapters>;
def VariantNativeBinding : ZKC_SpecialBinding<VariantSyntax, ["::zkc::data::VariantType"], "decodeVariantType", "encodeVariantType", CoreTypeAdapters>;
