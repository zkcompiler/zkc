// Native binding decisions owned by Curve.
include "zkc/Dialect/TypeBindings.td"
def CurveTypeAdapters : ZKC_TypeAdapterOwner<"zkc::protocol::type_adapters", "curveAdapters">;
def GroupNativeBinding : ZKC_DirectBinding<CatalogType_group, Group, "GroupAdapter", CurveTypeAdapters>;
def GroupsNativeBinding : ZKC_DirectBinding<CatalogType_groups, GroupVector, "GroupVectorAdapter", CurveTypeAdapters>;
