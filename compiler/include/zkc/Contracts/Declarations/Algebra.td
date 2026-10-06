// Logical contracts and curated exports owned by this domain.
def OpVectorGetF : ZKC_Root<"F", FieldDomain>;
def OpVectorGet : ZKC_Operation<"vector.get", [OpVectorGetF],
    [ZKC_Apply<TypeVector, [OpVectorGetF]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeField, [OpVectorGetF]>], [ZKC_Holds<CapabilityField, [OpVectorGetF]>]> {
  int ordinal = 24;
}
def ExportVectorGet : ZKC_OperationExport<"zkc::algebra", "vector_get",
    OpVectorGet, ["vector", "index"]>;

def OpVectorSliceF : ZKC_Root<"F", FieldDomain>;
def OpVectorSlice : ZKC_Operation<"vector.slice", [OpVectorSliceF],
    [ZKC_Apply<TypeVector, [OpVectorSliceF]>, ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeVector, [OpVectorSliceF]>], [ZKC_Holds<CapabilityField, [OpVectorSliceF]>]> {
  int ordinal = 25;
}
def ExportVectorSlice : ZKC_OperationExport<"zkc::algebra", "vector_slice",
    OpVectorSlice, ["vector", "index1", "index2"]>;

def OpVectorLengthF : ZKC_Root<"F", FieldDomain>;
def OpVectorLength : ZKC_Operation<"vector.length", [OpVectorLengthF],
    [ZKC_Apply<TypeVector, [OpVectorLengthF]>],
    [ZKC_Apply<TypeIndex, []>], [ZKC_Holds<CapabilityField, [OpVectorLengthF]>]> {
  int ordinal = 26;
  let facets = [ZKC_DomainValue<LengthValue, 0, 0, 1>];
}
def ExportVectorLength : ZKC_OperationExport<"zkc::algebra", "vector_length",
    OpVectorLength, ["vector"]>;

def OpVectorRotateF : ZKC_Root<"F", FieldDomain>;
def OpVectorRotate : ZKC_Operation<"vector.rotate", [OpVectorRotateF],
    [ZKC_Apply<TypeVector, [OpVectorRotateF]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeVector, [OpVectorRotateF]>], [ZKC_Holds<CapabilityField, [OpVectorRotateF]>]> {
  int ordinal = 27;
}
def ExportVectorRotate : ZKC_OperationExport<"zkc::algebra", "vector_rotate",
    OpVectorRotate, ["vector", "index"]>;

def OpVectorInterleaveF : ZKC_Root<"F", FieldDomain>;
def OpVectorInterleave : ZKC_Operation<"vector.interleave", [OpVectorInterleaveF],
    [ZKC_Apply<TypeVector, [OpVectorInterleaveF]>, ZKC_Apply<TypeVector, [OpVectorInterleaveF]>],
    [ZKC_Apply<TypeVector, [OpVectorInterleaveF]>], [ZKC_Holds<CapabilityField, [OpVectorInterleaveF]>]> {
  int ordinal = 28;
}
def ExportVectorInterleave : ZKC_OperationExport<"zkc::algebra", "vector_interleave",
    OpVectorInterleave, ["vector0", "vector1"]>;

def OpVectorPrefixProductF : ZKC_Root<"F", FieldDomain>;
def OpVectorPrefixProduct : ZKC_Operation<"vector.prefix_product", [OpVectorPrefixProductF],
    [ZKC_Apply<TypeVector, [OpVectorPrefixProductF]>],
    [ZKC_Apply<TypeVector, [OpVectorPrefixProductF]>], [ZKC_Holds<CapabilityField, [OpVectorPrefixProductF]>]> {
  int ordinal = 29;
}
def ExportVectorPrefixProduct : ZKC_OperationExport<"zkc::algebra", "vector_prefix_product",
    OpVectorPrefixProduct, ["vector"]>;

def OpVectorPrefixSumF : ZKC_Root<"F", FieldDomain>;
def OpVectorPrefixSum : ZKC_Operation<"vector.prefix_sum", [OpVectorPrefixSumF],
    [ZKC_Apply<TypeVector, [OpVectorPrefixSumF]>],
    [ZKC_Apply<TypeVector, [OpVectorPrefixSumF]>], [ZKC_Holds<CapabilityField, [OpVectorPrefixSumF]>]> {
  int ordinal = 30;
}
def ExportVectorPrefixSum : ZKC_OperationExport<"zkc::algebra", "vector_prefix_sum",
    OpVectorPrefixSum, ["vector"]>;

def OpVectorInverseF : ZKC_Root<"F", FieldDomain>;
def OpVectorInverse : ZKC_Operation<"vector.inverse", [OpVectorInverseF],
    [ZKC_Apply<TypeVector, [OpVectorInverseF]>],
    [ZKC_Apply<TypeVector, [OpVectorInverseF]>], [ZKC_Holds<CapabilityField, [OpVectorInverseF]>]> {
  int ordinal = 31;
}
def ExportVectorInverse : ZKC_OperationExport<"zkc::algebra", "vector_inverse",
    OpVectorInverse, ["vector"]>;

def OpVectorEmbedE : ZKC_Root<"E", FieldDomain>;
def OpVectorEmbedBaseField : ZKC_Project<OpVectorEmbedE, FieldBaseField>;
def OpVectorEmbed : ZKC_Operation<"vector.embed", [OpVectorEmbedE, OpVectorEmbedBaseField],
    [ZKC_Apply<TypeVector, [OpVectorEmbedBaseField]>],
    [ZKC_Apply<TypeVector, [OpVectorEmbedE]>], [ZKC_Holds<CapabilityExtensionField, [OpVectorEmbedE]>]> {
  int ordinal = 32;
}
def ExportVectorEmbed : ZKC_OperationExport<"zkc::algebra", "vector_embed",
    OpVectorEmbed, ["vector"]>;

def OpVectorFillF : ZKC_Root<"F", FieldDomain>;
def OpVectorFill : ZKC_Operation<"vector.fill", [OpVectorFillF],
    [ZKC_Apply<TypeField, [OpVectorFillF]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeVector, [OpVectorFillF]>], [ZKC_Holds<CapabilityField, [OpVectorFillF]>]> {
  int ordinal = 33;
}
def ExportVectorFill : ZKC_OperationExport<"zkc::algebra", "vector_fill",
    OpVectorFill, ["field", "index"]>;

def OpVectorGeometricF : ZKC_Root<"F", FieldDomain>;
def OpVectorGeometric : ZKC_Operation<"vector.geometric", [OpVectorGeometricF],
    [ZKC_Apply<TypeField, [OpVectorGeometricF]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeVector, [OpVectorGeometricF]>], [ZKC_Holds<CapabilityField, [OpVectorGeometricF]>]> {
  int ordinal = 34;
}
def ExportVectorGeometric : ZKC_OperationExport<"zkc::algebra", "vector_geometric",
    OpVectorGeometric, ["field", "index"]>;

def OpFieldFromIndexF : ZKC_Root<"F", FieldDomain>;
def OpFieldFromIndex : ZKC_Operation<"field.from_index", [OpFieldFromIndexF],
    [ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeField, [OpFieldFromIndexF]>], [ZKC_Holds<CapabilityField, [OpFieldFromIndexF]>]> {
  int ordinal = 35;
}
def ExportFieldFromIndex : ZKC_OperationExport<"zkc::algebra", "from_index",
    OpFieldFromIndex, ["index"]>;

def OpFieldSubF : ZKC_Root<"F", FieldDomain>;
def OpFieldSub : ZKC_Operation<"field.sub", [OpFieldSubF],
    [ZKC_Apply<TypeField, [OpFieldSubF]>, ZKC_Apply<TypeField, [OpFieldSubF]>],
    [ZKC_Apply<TypeField, [OpFieldSubF]>], [ZKC_Holds<CapabilityField, [OpFieldSubF]>]> {
  int ordinal = 45;
}
def ExportFieldSub : ZKC_OperationExport<"zkc::algebra", "sub",
    OpFieldSub, ["field0", "field1"]>;

def OpFieldNegF : ZKC_Root<"F", FieldDomain>;
def OpFieldNeg : ZKC_Operation<"field.neg", [OpFieldNegF],
    [ZKC_Apply<TypeField, [OpFieldNegF]>],
    [ZKC_Apply<TypeField, [OpFieldNegF]>], [ZKC_Holds<CapabilityField, [OpFieldNegF]>]> {
  int ordinal = 46;
}
def ExportFieldNeg : ZKC_OperationExport<"zkc::algebra", "neg",
    OpFieldNeg, ["field"]>;

def OpFieldInverseF : ZKC_Root<"F", FieldDomain>;
def OpFieldInverse : ZKC_Operation<"field.inverse", [OpFieldInverseF],
    [ZKC_Apply<TypeField, [OpFieldInverseF]>],
    [ZKC_Apply<TypeField, [OpFieldInverseF]>], [ZKC_Holds<CapabilityField, [OpFieldInverseF]>]> {
  int ordinal = 47;
}
def ExportFieldInverse : ZKC_OperationExport<"zkc::algebra", "inverse",
    OpFieldInverse, ["field"]>;

def OpFieldEmbedE : ZKC_Root<"E", FieldDomain>;
def OpFieldEmbedBaseField : ZKC_Project<OpFieldEmbedE, FieldBaseField>;
def OpFieldEmbed : ZKC_Operation<"field.embed", [OpFieldEmbedE, OpFieldEmbedBaseField],
    [ZKC_Apply<TypeField, [OpFieldEmbedBaseField]>],
    [ZKC_Apply<TypeField, [OpFieldEmbedE]>], [ZKC_Holds<CapabilityExtensionField, [OpFieldEmbedE]>]> {
  int ordinal = 48;
}
def ExportFieldEmbed : ZKC_OperationExport<"zkc::algebra", "embed",
    OpFieldEmbed, ["field"]>;

def OpMatrixMulVectorF : ZKC_Root<"F", FieldDomain>;
def OpMatrixMulVector : ZKC_Operation<"matrix.mul_vector", [OpMatrixMulVectorF],
    [ZKC_Apply<TypeMatrix, [OpMatrixMulVectorF]>, ZKC_Apply<TypeVector, [OpMatrixMulVectorF]>],
    [ZKC_Apply<TypeVector, [OpMatrixMulVectorF]>], [ZKC_Holds<CapabilityField, [OpMatrixMulVectorF]>]> {
  int ordinal = 49;
}
def ExportMatrixMulVector : ZKC_OperationExport<"zkc::algebra", "matrix_mul_vector",
    OpMatrixMulVector, ["matrix", "vector"]>;

def OpMatrixTransposeMulVectorF : ZKC_Root<"F", FieldDomain>;
def OpMatrixTransposeMulVector : ZKC_Operation<"matrix.transpose_mul_vector", [OpMatrixTransposeMulVectorF],
    [ZKC_Apply<TypeMatrix, [OpMatrixTransposeMulVectorF]>, ZKC_Apply<TypeVector, [OpMatrixTransposeMulVectorF]>],
    [ZKC_Apply<TypeVector, [OpMatrixTransposeMulVectorF]>], [ZKC_Holds<CapabilityField, [OpMatrixTransposeMulVectorF]>]> {
  int ordinal = 50;
}
def ExportMatrixTransposeMulVector : ZKC_OperationExport<"zkc::algebra", "matrix_transpose_mul_vector",
    OpMatrixTransposeMulVector, ["matrix", "vector"]>;

def OpMatrixBilinearF : ZKC_Root<"F", FieldDomain>;
def OpMatrixBilinear : ZKC_Operation<"matrix.bilinear", [OpMatrixBilinearF],
    [ZKC_Apply<TypeMatrix, [OpMatrixBilinearF]>, ZKC_Apply<TypeVector, [OpMatrixBilinearF]>, ZKC_Apply<TypeVector, [OpMatrixBilinearF]>],
    [ZKC_Apply<TypeField, [OpMatrixBilinearF]>], [ZKC_Holds<CapabilityField, [OpMatrixBilinearF]>]> {
  int ordinal = 51;
}
def ExportMatrixBilinear : ZKC_OperationExport<"zkc::algebra", "matrix_bilinear",
    OpMatrixBilinear, ["matrix", "vector1", "vector2"]>;

def OpMatrixDimensionF : ZKC_Root<"F", FieldDomain>;
def OpMatrixDimension : ZKC_Operation<"matrix.dimension", [OpMatrixDimensionF],
    [ZKC_Apply<TypeMatrix, [OpMatrixDimensionF]>], [ZKC_Apply<TypeIndex, []>],
    [ZKC_Holds<CapabilityField, [OpMatrixDimensionF]>]> {
  let parameters = NaturalParameter;
}
def ExportMatrixDimension : ZKC_OperationExport<"zkc::algebra", "matrix_dimension",
    OpMatrixDimension, ["matrix"]>;

def OpMatrixShapeCheckF : ZKC_Root<"F", FieldDomain>;
def OpMatrixShapeCheck : ZKC_Operation<"matrix.shape_check", [OpMatrixShapeCheckF],
    [ZKC_Apply<TypeMatrix, [OpMatrixShapeCheckF]>],
    [ZKC_Apply<TypeBool, []>], [ZKC_Holds<CapabilityField, [OpMatrixShapeCheckF]>]> {
  int ordinal = 52;
  let parameters = MatrixShape;
}
def ExportMatrixShapeCheck : ZKC_OperationExport<"zkc::algebra", "matrix_shape_check",
    OpMatrixShapeCheck, ["matrix"]>;

def OpMatrixIdentityCheckF : ZKC_Root<"F", FieldDomain>;
def OpMatrixIdentityCheck : ZKC_Operation<"matrix.identity_check", [OpMatrixIdentityCheckF],
    [ZKC_Apply<TypeMatrix, [OpMatrixIdentityCheckF]>],
    [ZKC_Apply<TypeBool, []>], [ZKC_Holds<CapabilityField, [OpMatrixIdentityCheckF]>]> {
  int ordinal = 53;
  let parameters = MatrixIdentity;
}
def ExportMatrixIdentityCheck : ZKC_OperationExport<"zkc::algebra", "matrix_identity_check",
    OpMatrixIdentityCheck, ["matrix"]>;

def OpVectorConstantF : ZKC_Root<"F", FieldDomain>;
def OpVectorConstant : ZKC_Operation<"vector.constant", [OpVectorConstantF],
    [],
    [ZKC_Apply<TypeVector, [OpVectorConstantF]>], [ZKC_Holds<CapabilityField, [OpVectorConstantF]>]> {
  int ordinal = 54;
  let parameters = FieldLiterals;
  let parameterField = OpVectorConstantF;
}
def ExportVectorConstant : ZKC_OperationExport<"zkc::algebra", "vector_constant",
    OpVectorConstant, []>;

def OpVectorScatterSumF : ZKC_Root<"F", FieldDomain>;
def OpVectorScatterSum : ZKC_Operation<"vector.scatter_sum", [OpVectorScatterSumF],
    [ZKC_Apply<TypeVector, [OpVectorScatterSumF]>],
    [ZKC_Apply<TypeVector, [OpVectorScatterSumF]>], [ZKC_Holds<CapabilityField, [OpVectorScatterSumF]>]> {
  int ordinal = 55;
  let parameters = ScatterIndices;
}
def ExportVectorScatterSum : ZKC_OperationExport<"zkc::algebra", "vector_scatter_sum",
    OpVectorScatterSum, ["vector"]>;

def OpVectorEmptyF : ZKC_Root<"F", FieldDomain>;
def OpVectorEmpty : ZKC_Operation<"vector.empty", [OpVectorEmptyF],
    [],
    [ZKC_Apply<TypeVector, [OpVectorEmptyF]>], [ZKC_Holds<CapabilityField, [OpVectorEmptyF]>]> {
  int ordinal = 56;
}
def ExportVectorEmpty : ZKC_OperationExport<"zkc::algebra", "vector_empty",
    OpVectorEmpty, []>;

def OpVectorAppendF : ZKC_Root<"F", FieldDomain>;
def OpVectorAppend : ZKC_Operation<"vector.append", [OpVectorAppendF],
    [ZKC_Apply<TypeVector, [OpVectorAppendF]>, ZKC_Apply<TypeField, [OpVectorAppendF]>],
    [ZKC_Apply<TypeVector, [OpVectorAppendF]>], [ZKC_Holds<CapabilityField, [OpVectorAppendF]>]> {
  int ordinal = 57;
}
def ExportVectorAppend : ZKC_OperationExport<"zkc::algebra", "vector_append",
    OpVectorAppend, ["vector", "field"]>;

def OpVectorSplatF : ZKC_Root<"F", FieldDomain>;
def OpVectorSplat : ZKC_Operation<"vector.splat", [OpVectorSplatF],
    [ZKC_Apply<TypeField, [OpVectorSplatF]>],
    [ZKC_Apply<TypeVector, [OpVectorSplatF]>], [ZKC_Holds<CapabilityField, [OpVectorSplatF]>]> {
  int ordinal = 58;
  let parameters = ExtentParameter;
}
def ExportVectorSplat : ZKC_OperationExport<"zkc::algebra", "vector_splat",
    OpVectorSplat, ["field"]>;

def OpVectorPowersF : ZKC_Root<"F", FieldDomain>;
def OpVectorPowers : ZKC_Operation<"vector.powers", [OpVectorPowersF],
    [ZKC_Apply<TypeField, [OpVectorPowersF]>],
    [ZKC_Apply<TypeVector, [OpVectorPowersF]>], [ZKC_Holds<CapabilityField, [OpVectorPowersF]>]> {
  int ordinal = 59;
  let parameters = ExtentParameter;
}
def ExportVectorPowers : ZKC_OperationExport<"zkc::algebra", "vector_powers",
    OpVectorPowers, ["field"]>;

def OpVectorAddF : ZKC_Root<"F", FieldDomain>;
def OpVectorAdd : ZKC_Operation<"vector.add", [OpVectorAddF],
    [ZKC_Apply<TypeVector, [OpVectorAddF]>, ZKC_Apply<TypeVector, [OpVectorAddF]>],
    [ZKC_Apply<TypeVector, [OpVectorAddF]>], [ZKC_Holds<CapabilityField, [OpVectorAddF]>]> {
  int ordinal = 60;
}
def ExportVectorAdd : ZKC_OperationExport<"zkc::algebra", "vector_add",
    OpVectorAdd, ["vector0", "vector1"]>;

def OpVectorSubF : ZKC_Root<"F", FieldDomain>;
def OpVectorSub : ZKC_Operation<"vector.sub", [OpVectorSubF],
    [ZKC_Apply<TypeVector, [OpVectorSubF]>, ZKC_Apply<TypeVector, [OpVectorSubF]>],
    [ZKC_Apply<TypeVector, [OpVectorSubF]>], [ZKC_Holds<CapabilityField, [OpVectorSubF]>]> {
  int ordinal = 61;
}
def ExportVectorSub : ZKC_OperationExport<"zkc::algebra", "vector_sub",
    OpVectorSub, ["vector0", "vector1"]>;

def OpVectorMulF : ZKC_Root<"F", FieldDomain>;
def OpVectorMul : ZKC_Operation<"vector.mul", [OpVectorMulF],
    [ZKC_Apply<TypeVector, [OpVectorMulF]>, ZKC_Apply<TypeVector, [OpVectorMulF]>],
    [ZKC_Apply<TypeVector, [OpVectorMulF]>], [ZKC_Holds<CapabilityField, [OpVectorMulF]>]> {
  int ordinal = 62;
  let facets = [ZKC_Diagonal<0, 1, 0>];
}
def ExportVectorMul : ZKC_OperationExport<"zkc::algebra", "vector_mul",
    OpVectorMul, ["vector0", "vector1"]>;

def OpVectorDotF : ZKC_Root<"F", FieldDomain>;
def OpVectorDot : ZKC_Operation<"vector.dot", [OpVectorDotF],
    [ZKC_Apply<TypeVector, [OpVectorDotF]>, ZKC_Apply<TypeVector, [OpVectorDotF]>],
    [ZKC_Apply<TypeField, [OpVectorDotF]>], [ZKC_Holds<CapabilityField, [OpVectorDotF]>]> {
  int ordinal = 63;
  let facets = [ZKC_Contraction<0, 1>];
}
def ExportVectorDot : ZKC_OperationExport<"zkc::algebra", "vector_dot",
    OpVectorDot, ["vector0", "vector1"]>;

def OpVectorConcatF : ZKC_Root<"F", FieldDomain>;
def OpVectorConcat : ZKC_Operation<"vector.concat", [OpVectorConcatF],
    [ZKC_Apply<TypeVector, [OpVectorConcatF]>, ZKC_Apply<TypeVector, [OpVectorConcatF]>],
    [ZKC_Apply<TypeVector, [OpVectorConcatF]>], [ZKC_Holds<CapabilityField, [OpVectorConcatF]>]> {
  int ordinal = 64;
}
def ExportVectorConcat : ZKC_OperationExport<"zkc::algebra", "vector_concat",
    OpVectorConcat, ["vector0", "vector1"]>;

def OpVectorKroneckerF : ZKC_Root<"F", FieldDomain>;
def OpVectorKronecker : ZKC_Operation<"vector.kronecker", [OpVectorKroneckerF],
    [ZKC_Apply<TypeVector, [OpVectorKroneckerF]>, ZKC_Apply<TypeVector, [OpVectorKroneckerF]>],
    [ZKC_Apply<TypeVector, [OpVectorKroneckerF]>], [ZKC_Holds<CapabilityField, [OpVectorKroneckerF]>]> {
  int ordinal = 65;
}
def ExportVectorKronecker : ZKC_OperationExport<"zkc::algebra", "vector_kronecker",
    OpVectorKronecker, ["vector0", "vector1"]>;

def OpVectorMatvecF : ZKC_Root<"F", FieldDomain>;
def OpVectorMatvec : ZKC_Operation<"vector.matvec", [OpVectorMatvecF],
    [ZKC_Apply<TypeVector, [OpVectorMatvecF]>, ZKC_Apply<TypeVector, [OpVectorMatvecF]>],
    [ZKC_Apply<TypeVector, [OpVectorMatvecF]>], [ZKC_Holds<CapabilityField, [OpVectorMatvecF]>]> {
  int ordinal = 66;
  let parameters = MatrixVector;
}
def ExportVectorMatvec : ZKC_OperationExport<"zkc::algebra", "vector_matvec",
    OpVectorMatvec, ["vector0", "vector1"]>;

def OpVectorScaleF : ZKC_Root<"F", FieldDomain>;
def OpVectorScale : ZKC_Operation<"vector.scale", [OpVectorScaleF],
    [ZKC_Apply<TypeVector, [OpVectorScaleF]>, ZKC_Apply<TypeField, [OpVectorScaleF]>],
    [ZKC_Apply<TypeVector, [OpVectorScaleF]>], [ZKC_Holds<CapabilityField, [OpVectorScaleF]>]> {
  int ordinal = 67;
}
def ExportVectorScale : ZKC_OperationExport<"zkc::algebra", "vector_scale",
    OpVectorScale, ["vector", "field"]>;

def OpVectorSumF : ZKC_Root<"F", FieldDomain>;
def OpVectorSum : ZKC_Operation<"vector.sum", [OpVectorSumF],
    [ZKC_Apply<TypeVector, [OpVectorSumF]>],
    [ZKC_Apply<TypeField, [OpVectorSumF]>], [ZKC_Holds<CapabilityField, [OpVectorSumF]>]> {
  int ordinal = 68;
}
def ExportVectorSum : ZKC_OperationExport<"zkc::algebra", "vector_sum",
    OpVectorSum, ["vector"]>;

def OpVectorSplitF : ZKC_Root<"F", FieldDomain>;
def OpVectorSplit : ZKC_Operation<"vector.split", [OpVectorSplitF],
    [ZKC_Apply<TypeVector, [OpVectorSplitF]>],
    [ZKC_Apply<TypeVector, [OpVectorSplitF]>, ZKC_Apply<TypeVector, [OpVectorSplitF]>], [ZKC_Holds<CapabilityField, [OpVectorSplitF]>]> {
  int ordinal = 69;
}
def ExportVectorSplit : ZKC_OperationExport<"zkc::algebra", "vector_split",
    OpVectorSplit, ["vector"]>;

def OpVectorAtF : ZKC_Root<"F", FieldDomain>;
def OpVectorAt : ZKC_Operation<"vector.at", [OpVectorAtF],
    [ZKC_Apply<TypeVector, [OpVectorAtF]>],
    [ZKC_Apply<TypeField, [OpVectorAtF]>], [ZKC_Holds<CapabilityField, [OpVectorAtF]>]> {
  int ordinal = 70;
  let parameters = ExtentParameter;
}
def ExportVectorAt : ZKC_OperationExport<"zkc::algebra", "vector_at",
    OpVectorAt, ["vector"]>;

def OpVectorLengthCheckF : ZKC_Root<"F", FieldDomain>;
def OpVectorLengthCheck : ZKC_Operation<"vector.length_check", [OpVectorLengthCheckF],
    [ZKC_Apply<TypeVector, [OpVectorLengthCheckF]>],
    [ZKC_Apply<TypeBool, []>], [ZKC_Holds<CapabilityField, [OpVectorLengthCheckF]>]> {
  int ordinal = 71;
  let parameters = ExtentParameter;
}
def ExportVectorLengthCheck : ZKC_OperationExport<"zkc::algebra", "vector_length_check",
    OpVectorLengthCheck, ["vector"]>;

def OpVectorGatherF : ZKC_Root<"F", FieldDomain>;
def OpVectorGather : ZKC_Operation<"vector.gather", [OpVectorGatherF],
    [ZKC_Apply<TypeVector, [OpVectorGatherF]>],
    [ZKC_Apply<TypeVector, [OpVectorGatherF]>], [ZKC_Holds<CapabilityField, [OpVectorGatherF]>]> {
  int ordinal = 72;
  let parameters = GatherIndices;
}
def ExportVectorGather : ZKC_OperationExport<"zkc::algebra", "vector_gather",
    OpVectorGather, ["vector"]>;

def OpVectorFromPointF : ZKC_Root<"F", FieldDomain>;
def OpVectorFromPoint : ZKC_Operation<"vector.from_point", [OpVectorFromPointF],
    [ZKC_Apply<TypePoint, [OpVectorFromPointF]>],
    [ZKC_Apply<TypeVector, [OpVectorFromPointF]>], [ZKC_Holds<CapabilityField, [OpVectorFromPointF]>]> {
  int ordinal = 73;
}
def ExportVectorFromPoint : ZKC_OperationExport<"zkc::algebra", "vector_from_point",
    OpVectorFromPoint, ["point"]>;

def OpVectorFromTableF : ZKC_Root<"F", FieldDomain>;
def OpVectorFromTable : ZKC_Operation<"vector.from_table", [OpVectorFromTableF],
    [ZKC_Apply<TypeTable, [OpVectorFromTableF]>],
    [ZKC_Apply<TypeVector, [OpVectorFromTableF]>], [ZKC_Holds<CapabilityField, [OpVectorFromTableF]>]> {
  int ordinal = 74;
}
def ExportVectorFromTable : ZKC_OperationExport<"zkc::algebra", "vector_from_table",
    OpVectorFromTable, ["table"]>;

def OpVectorToPointF : ZKC_Root<"F", FieldDomain>;
def OpVectorToPoint : ZKC_Operation<"vector.to_point", [OpVectorToPointF],
    [ZKC_Apply<TypeVector, [OpVectorToPointF]>],
    [ZKC_Apply<TypePoint, [OpVectorToPointF]>], [ZKC_Holds<CapabilityField, [OpVectorToPointF]>]> {
  int ordinal = 75;
}
def ExportVectorToPoint : ZKC_OperationExport<"zkc::algebra", "vector_to_point",
    OpVectorToPoint, ["vector"]>;

def OpVectorToTableF : ZKC_Root<"F", FieldDomain>;
def OpVectorToTable : ZKC_Operation<"vector.to_table", [OpVectorToTableF],
    [ZKC_Apply<TypeVector, [OpVectorToTableF]>],
    [ZKC_Apply<TypeTable, [OpVectorToTableF]>], [ZKC_Holds<CapabilityField, [OpVectorToTableF]>]> {
  int ordinal = 76;
}
def ExportVectorToTable : ZKC_OperationExport<"zkc::algebra", "vector_to_table",
    OpVectorToTable, ["vector"]>;

def OpFieldConstantF : ZKC_Root<"F", FieldDomain>;
def OpFieldConstant : ZKC_Operation<"field.constant", [OpFieldConstantF],
    [],
    [ZKC_Apply<TypeField, [OpFieldConstantF]>], [ZKC_Holds<CapabilityField, [OpFieldConstantF]>]> {
  int ordinal = 93;
  let parameters = FieldLiteral;
  let parameterField = OpFieldConstantF;
  let facets = [PublicReplay, ZKC_DomainValue<ConstantValue, 0, 0, 1>];
}
def ExportFieldConstant : ZKC_OperationExport<"zkc::algebra", "constant",
    OpFieldConstant, []>;

def OpFieldAddF : ZKC_Root<"F", FieldDomain>;
def OpFieldAdd : ZKC_Operation<"field.add", [OpFieldAddF],
    [ZKC_Apply<TypeField, [OpFieldAddF]>, ZKC_Apply<TypeField, [OpFieldAddF]>],
    [ZKC_Apply<TypeField, [OpFieldAddF]>], [ZKC_Holds<CapabilityField, [OpFieldAddF]>]> {
  int ordinal = 94;
  let facets = [PublicReplay];
}
def ExportFieldAdd : ZKC_OperationExport<"zkc::algebra", "add",
    OpFieldAdd, ["field0", "field1"]>;

def OpFieldMulF : ZKC_Root<"F", FieldDomain>;
def OpFieldMul : ZKC_Operation<"field.mul", [OpFieldMulF],
    [ZKC_Apply<TypeField, [OpFieldMulF]>, ZKC_Apply<TypeField, [OpFieldMulF]>],
    [ZKC_Apply<TypeField, [OpFieldMulF]>], [ZKC_Holds<CapabilityField, [OpFieldMulF]>]> {
  int ordinal = 95;
  let facets = [PublicReplay, ZKC_DomainValue<MultiplyValue, 0, 0, 1>];
}
def ExportFieldMul : ZKC_OperationExport<"zkc::algebra", "mul",
    OpFieldMul, ["field0", "field1"]>;

def OpFieldEqualF : ZKC_Root<"F", FieldDomain>;
def OpFieldEqual : ZKC_Operation<"field.equal", [OpFieldEqualF],
    [ZKC_Apply<TypeField, [OpFieldEqualF]>, ZKC_Apply<TypeField, [OpFieldEqualF]>],
    [ZKC_Apply<TypeBool, []>], [ZKC_Holds<CapabilityField, [OpFieldEqualF]>]> {
  int ordinal = 96;
  let facets = [PublicReplay];
}
def ExportFieldEqual : ZKC_OperationExport<"zkc::algebra", "equal",
    OpFieldEqual, ["field0", "field1"]>;

def OperatorFieldAdd0 : ZKC_Operator<"+", [TypeField, TypeField], OpFieldAdd, [0, 1]>;
def OperatorFieldSub1 : ZKC_Operator<"-", [TypeField, TypeField], OpFieldSub, [0, 1]>;
def OperatorFieldMul2 : ZKC_Operator<"*", [TypeField, TypeField], OpFieldMul, [0, 1]>;
def OperatorFieldNeg3 : ZKC_Operator<"-", [TypeField], OpFieldNeg, [0]>;
def OperatorVectorAdd8 : ZKC_Operator<"+", [TypeVector, TypeVector], OpVectorAdd, [0, 1]>;
def OperatorVectorSub9 : ZKC_Operator<"-", [TypeVector, TypeVector], OpVectorSub, [0, 1]>;
def OperatorVectorScale10 : ZKC_Operator<"*", [TypeVector, TypeField], OpVectorScale, [0, 1]>;
def OperatorVectorScale11 : ZKC_Operator<"*", [TypeField, TypeVector], OpVectorScale, [1, 0]>;

// Exact finite vector equality, including length. No padding or reduction.
def OpVectorEqualF : ZKC_Root<"F", FieldDomain>;
def OpVectorEqual : ZKC_Operation<"vector.equal", [OpVectorEqualF],
    [ZKC_Apply<TypeVector, [OpVectorEqualF]>, ZKC_Apply<TypeVector, [OpVectorEqualF]>],
    [ZKC_Apply<TypeBool, []>], [ZKC_Holds<CapabilityCommRing, [OpVectorEqualF]>]> {
  int ordinal = 159;
}
def ExportVectorEqual : ZKC_OperationExport<"zkc::algebra", "vector_equal",
    OpVectorEqual, ["left", "right"]>;
