// Native collection binding decisions owned by Data.
include "zkc/Dialect/TypeBindings.td"
def DataTypeAdapters : ZKC_TypeAdapterOwner<"zkc::protocol::type_adapters", "dataAdapters">;
def VectorNativeBinding : ZKC_DirectBinding<CatalogType_vector, FieldVector, "FieldVectorAdapter", DataTypeAdapters>;
def MatrixNativeBinding : ZKC_DirectBinding<CatalogType_matrix, FieldMatrix, "FieldMatrixAdapter", DataTypeAdapters>;
def FixedVectorNativeBinding : ZKC_DirectBinding<CatalogType_fixed_5fvector, FixedVector, "FixedVectorAdapter", DataTypeAdapters>;
def IndicesNativeBinding : ZKC_DirectBinding<CatalogType_indices, Indices, "IndicesAdapter", DataTypeAdapters>;
def ArrayNativeBinding : ZKC_DirectBinding<CatalogType_field_5farray, FieldArray, "FieldArrayAdapter", DataTypeAdapters>;
def GroupsNativeBinding : ZKC_DirectBinding<CatalogType_groups, GroupVector, "GroupVectorAdapter", DataTypeAdapters>;
def SequenceNativeBinding : ZKC_CustomBinding<CatalogType_sequence, ["::zkc::data::SequenceType"], "decodeSequence", "encodeSequence", "sequenceArguments", "constructSequence", DataTypeAdapters>;
def BytesNativeBinding : ZKC_DirectBinding<CatalogType_bytes, Bytes, "BytesAdapter", DataTypeAdapters>;
def VariantNativeBinding : ZKC_SpecialBinding<VariantSyntax, ["::zkc::data::VariantType"], "decodeVariantType", "encodeVariantType", DataTypeAdapters>;
