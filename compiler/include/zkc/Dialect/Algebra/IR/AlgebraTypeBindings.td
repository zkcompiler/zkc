// Native binding decisions owned by Algebra.
include "zkc/Dialect/TypeBindings.td"
def AlgebraTypeAdapters : ZKC_TypeAdapterOwner<"zkc::protocol::type_adapters", "algebraAdapters">;
def FieldNativeBinding : ZKC_DirectBinding<TypeField, Field, "FieldAdapter", AlgebraTypeAdapters>;
def VectorNativeBinding : ZKC_CustomBinding<TypeVector, ["::mlir::RankedTensorType"], "decodeDomainVector<zkc::algebra::FieldType>", "encodeDomainVector<zkc::algebra::FieldType>", AlgebraTypeAdapters>;
def MatrixNativeBinding : ZKC_CustomBinding<TypeMatrix, ["::mlir::RankedTensorType"], "decodeMatrix", "encodeMatrix", AlgebraTypeAdapters>;
def FixedVectorNativeBinding : ZKC_DirectBinding<TypeFixedVector, FixedVector, "FixedVectorAdapter", AlgebraTypeAdapters>;
def IndicesNativeBinding : ZKC_CustomBinding<TypeIndices, ["::mlir::RankedTensorType"], "decodeIndices", "encodeIndices", AlgebraTypeAdapters>;
def ArrayNativeBinding : ZKC_CustomBinding<TypeFieldArray,
    ["::mlir::RankedTensorType"], "decodeFieldArray", "encodeFieldArray", AlgebraTypeAdapters>;
