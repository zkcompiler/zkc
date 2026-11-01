// Native binding decisions owned by Algebra.
include "zkc/Dialect/TypeBindings.td"
def AlgebraTypeAdapters : ZKC_TypeAdapterOwner<"zkc::protocol::type_adapters", "algebraAdapters">;
def FieldNativeBinding : ZKC_DirectBinding<CatalogType_field, Field, "FieldAdapter", AlgebraTypeAdapters>;
