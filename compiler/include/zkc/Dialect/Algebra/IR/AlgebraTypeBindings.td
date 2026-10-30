// Native binding decisions owned by Algebra.
include "zkc/Dialect/TypeBindings.td"
def AlgebraTypeAdapters : ZKC_TypeAdapterOwner<"zkc::protocol::type_adapters", "algebraAdapters">;
def FieldNativeBinding : ZKC_DirectBinding<CatalogType_field, Field, "FieldAdapter", AlgebraTypeAdapters>;
def VectorNativeBinding : ZKC_DirectBinding<CatalogType_vector, FieldVector, "FieldVectorAdapter", AlgebraTypeAdapters>;
def MatrixNativeBinding : ZKC_DirectBinding<CatalogType_matrix, FieldMatrix, "FieldMatrixAdapter", AlgebraTypeAdapters>;
def FixedVectorNativeBinding : ZKC_DirectBinding<CatalogType_fixed_5fvector, FixedVector, "FixedVectorAdapter", AlgebraTypeAdapters>;
def IndicesNativeBinding : ZKC_DirectBinding<CatalogType_indices, Indices, "IndicesAdapter", AlgebraTypeAdapters>;
def ArrayNativeBinding : ZKC_DirectBinding<CatalogType_field_5farray, FieldArray, "FieldArrayAdapter", AlgebraTypeAdapters>;
