include "zkc/Dialect/TypeBindings.td"
def RuntimeTypeAdapters : ZKC_TypeAdapterOwner<"zkc::protocol::type_adapters", "runtimeAdapters">;
def QuotientMatrixNativeBinding : ZKC_DirectBinding<TypeQuotientMatrix, RuntimeQuotientMatrix, "QuotientMatrixAdapter", RuntimeTypeAdapters>;
