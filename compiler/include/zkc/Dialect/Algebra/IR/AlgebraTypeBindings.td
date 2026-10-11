// Native binding decisions owned by Algebra.
include "zkc/Dialect/TypeBindings.td"
def AlgebraTypeAdapters : ZKC_TypeAdapterOwner<"zkc::protocol::type_adapters", "algebraAdapters">;
def FieldNativeBinding : ZKC_DirectBinding<TypeField, Field, "FieldAdapter", AlgebraTypeAdapters>;
def VectorNativeBinding : ZKC_DirectBinding<TypeVector, FieldVector, "FieldVectorAdapter", AlgebraTypeAdapters>;
def MatrixNativeBinding : ZKC_DirectBinding<TypeMatrix, FieldMatrix, "FieldMatrixAdapter", AlgebraTypeAdapters>;
def FixedVectorNativeBinding : ZKC_DirectBinding<TypeFixedVector, FixedVector, "FixedVectorAdapter", AlgebraTypeAdapters>;
def IndicesNativeBinding : ZKC_DirectBinding<TypeIndices, Indices, "IndicesAdapter", AlgebraTypeAdapters>;
def ArrayNativeBinding : ZKC_DirectBinding<TypeFieldArray, FieldArray, "FieldArrayAdapter", AlgebraTypeAdapters>;
