// Native binding decisions owned by Algebra.
include "zkc/Dialect/TypeBindings.td"
def AlgebraTypeAdapters : ZKC_TypeAdapterOwner<"zkc::protocol::type_adapters", "algebraAdapters">;
def FieldNativeBinding : ZKC_DirectBinding<TypeField, Field, "FieldAdapter", AlgebraTypeAdapters>;
def VectorNativeBinding : ZKC_CustomBinding<TypeVector, ["::mlir::RankedTensorType"], "decodeDomainVector<FieldType>", "encodeDomainVector<FieldType>", AlgebraTypeAdapters>;
def MatrixNativeBinding : ZKC_DirectBinding<TypeMatrix, Matrix, "MatrixAdapter", AlgebraTypeAdapters>;
def FixedVectorNativeBinding : ZKC_DirectBinding<TypeFixedVector, FixedVector, "FixedVectorAdapter", AlgebraTypeAdapters>;
def IndicesNativeBinding : ZKC_CustomBinding<TypeIndices, ["::mlir::RankedTensorType"], "decodeIndices", "encodeIndices", AlgebraTypeAdapters>;
