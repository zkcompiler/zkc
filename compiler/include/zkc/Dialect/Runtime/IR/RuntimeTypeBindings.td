include "zkc/Dialect/TypeBindings.td"
def RuntimeTypeAdapters : ZKC_TypeAdapterOwner<"zkc::protocol::type_adapters", "runtimeAdapters">;
def QuotientMatrixNativeBinding : ZKC_DirectBinding<CatalogType_quotient_5fmatrix, RuntimeQuotientMatrix, "QuotientMatrixAdapter", RuntimeTypeAdapters>;
