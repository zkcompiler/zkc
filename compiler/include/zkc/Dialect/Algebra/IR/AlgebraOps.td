#ifndef ZKC_DIALECT_ALGEBRA_IR_ALGEBRAOPS_TD
#define ZKC_DIALECT_ALGEBRA_IR_ALGEBRAOPS_TD

include "zkc/Dialect/Types.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "zkc/Dialect/BoundOperations.td"
include "zkc/Interfaces/Mathematical.td"
include "zkc/Interfaces/PreparationCallable.td"

class TotalMathOp<Dialect dialect, string mnemonic, Type lhs, Type rhs,
                  Type result, list<Trait> traits = []>
    : Op<dialect, mnemonic, !listconcat([Pure], traits)> {
  let arguments = (ins lhs:$lhs, rhs:$rhs);
  let results = (outs result:$value);
  let hasVerifier = 1;
  let assemblyFormat = "$lhs `,` $rhs attr-dict `:` functional-type(operands, results)";
}

def FieldCompareOp : BoundOp<AlgebraDialect, "exec.field_equal", [OpFieldEqual]>;

def FieldConstantOp : BoundOp<AlgebraDialect, "exec.field_constant", [OpFieldConstant]>;

def CurveAddOp : BoundOp<AlgebraDialect, "exec.group_add", [OpCurveAdd]>;

def CurveAppendOp : BoundOp<AlgebraDialect, "exec.group_append", [OpCurveAppend]>;

def CurveAtOp : BoundOp<AlgebraDialect, "exec.group_at", [OpCurveAt]>;

def CurveConcatOp : BoundOp<AlgebraDialect, "exec.group_concat", [OpCurveConcat]>;

def CurveEmptyOp : BoundOp<AlgebraDialect, "exec.group_empty", [OpCurveEmpty]>;

def CurveEqualOp : BoundOp<AlgebraDialect, "exec.group_equal", [OpCurveEqual]>;

def CurveGeneratorOp : BoundOp<AlgebraDialect, "exec.group_generator", [OpCurveGenerator]>;

def CurveIdentityOp : BoundOp<AlgebraDialect, "exec.group_identity", [OpCurveIdentity]>;

def CurveGetOp : BoundOp<AlgebraDialect, "exec.group_get", [OpCurveGet]>;

def CurveLengthOp : BoundOp<AlgebraDialect, "exec.group_length", [OpCurveLength]>;

def CurveMSMOp : BoundOp<AlgebraDialect, "exec.group_msm", [OpCurveMsm], [DeclareOpInterfaceMethods<DiagonalContractionInterface>]>;

def CurveNegateOp : BoundOp<AlgebraDialect, "exec.group_negate", [OpCurveNeg]>;

def CurveNonidentityOp : BoundOp<AlgebraDialect, "exec.group_nonidentity", [OpCurveNonidentity]>;

def CurveScaleOp : BoundOp<AlgebraDialect, "exec.group_scale", [OpCurveScale]>;

def CurveScaleEachOp : BoundOp<AlgebraDialect, "exec.group_scale_each", [OpCurveScaleEach], [DeclareOpInterfaceMethods<DiagonalProducerInterface>]>;

def CurveSplitOp : BoundOp<AlgebraDialect, "exec.group_split", [OpCurveSplit]>;

def CurveVectorAddOp : BoundOp<AlgebraDialect, "exec.group_vector_add", [OpCurveVectorAdd]>;

def CurveVectorScaleOp : BoundOp<AlgebraDialect, "exec.group_vector_scale", [OpCurveVectorScale]>;

def FieldEmbedOp : BoundOp<AlgebraDialect, "exec.field_embed", [OpFieldEmbed]>;

def FieldAddOp : TotalMathOp<AlgebraDialect, "field_add", Field, Field, Field, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;

def FieldEqualOp : TotalMathOp<AlgebraDialect, "field_equal", Field, Field, I1, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;

def FieldFromIndexOp : BoundOp<AlgebraDialect, "exec.field_from_index", [OpFieldFromIndex]>;

def FieldMultiplyOp : TotalMathOp<AlgebraDialect, "field_multiply", Field, Field, Field, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;

def FixedVectorDotOp : BoundOp<AlgebraDialect, "exec.fixed_vector_dot",
                              [OpFixedVectorDot]>;

def FixedVectorFromVectorOp : BoundOp<AlgebraDialect, "exec.fixed_vector_from_vector",
                                     [OpFixedVectorFromVector]>;

def FixedVectorToVectorOp : BoundOp<AlgebraDialect, "exec.fixed_vector_to_vector",
                                   [OpFixedVectorToVector]>;

def GroupAddOp : TotalMathOp<AlgebraDialect, "group_add", Group, Group, Group, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;

def GroupIdentityOp : Op<AlgebraDialect, "group_identity",
    [Pure, DeclareOpInterfaceMethods<MathematicalOpInterface>]> {
  let summary = "The identity of the result's nominal group";
  let results = (outs Group:$value);
  let hasVerifier = 1;
  let assemblyFormat = "attr-dict `:` type($value)";
}

def GroupEqualOp : TotalMathOp<AlgebraDialect, "group_equal", Group, Group, I1, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;

def GroupScaleOp : TotalMathOp<AlgebraDialect, "group_scale", Group, Field, Group, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;

def IndexAddOp : BoundOp<AlgebraDialect, "exec.index_add", [OpIndexAdd]>;

def IndexConstantOp : BoundOp<AlgebraDialect, "exec.index_constant", [OpIndexConstant]>;

def IndexDivOp : BoundOp<AlgebraDialect, "exec.index_div", [OpIndexDiv]>;

def IndexEqualOp : BoundOp<AlgebraDialect, "exec.index_equal", [OpIndexEqual]>;

def IndexLessOp : BoundOp<AlgebraDialect, "exec.index_less", [OpIndexLess]>;

def IndexModOp : BoundOp<AlgebraDialect, "exec.index_mod", [OpIndexMod]>;

def IndexMulOp : BoundOp<AlgebraDialect, "exec.index_mul", [OpIndexMul]>;

def IndexSubOp : BoundOp<AlgebraDialect, "exec.index_sub", [OpIndexSub]>;

def IndicesAppendOp : BoundOp<AlgebraDialect, "exec.indices_append", [OpIndicesAppend]>;

def IndicesAtOp : BoundOp<AlgebraDialect, "exec.indices_at", [OpIndicesAt]>;

def IndicesEmptyOp : BoundOp<AlgebraDialect, "exec.indices_empty", [OpIndicesEmpty]>;

def IndicesLengthOp : BoundOp<AlgebraDialect, "exec.indices_length", [OpIndicesLength]>;

def QuotientAddOp : BoundOp<AlgebraDialect, "exec.quotient_add", [OpQuotientAdd]>;
def QuotientSubtractOp : BoundOp<AlgebraDialect, "exec.quotient_subtract", [OpQuotientSubtract]>;
def QuotientMultiplyOp : BoundOp<AlgebraDialect, "exec.quotient_multiply", [OpQuotientMultiply]>;
def QuotientNormWithinOp : BoundOp<AlgebraDialect, "exec.quotient_norm_within", [OpQuotientNormWithin]>;
def QuotientProjectOp : BoundOp<AlgebraDialect, "exec.quotient_project", [OpQuotientProject]>;
def QuotientNTTOp : BoundOp<AlgebraDialect, "exec.quotient_ntt", [OpQuotientNTT]>;
def QuotientINTTOp : BoundOp<AlgebraDialect, "exec.quotient_intt", [OpQuotientINTT]>;
def QuotientPointwiseOp : BoundOp<AlgebraDialect, "exec.quotient_pointwise", [OpQuotientPointwise]>;

def FieldInverseOp : BoundOp<AlgebraDialect, "exec.field_inverse", [OpFieldInverse]>;

def MatrixBilinearOp : BoundOp<AlgebraDialect, "exec.matrix_bilinear", [OpMatrixBilinear]>;

def MatrixIdentityCheckOp : BoundOp<AlgebraDialect, "exec.matrix_identity_check", [OpMatrixIdentityCheck]>;

def NumericalMapOp : BoundOp<AlgebraDialect, "exec.numerical_map", [OpNumericalMap]>;
def NumericalSumOp : BoundOp<AlgebraDialect, "exec.numerical_sum", [OpNumericalSum]>;
def NumericalProductOp : BoundOp<AlgebraDialect, "exec.numerical_product", [OpNumericalProduct]>;

def RingPointOp : BoundOp<AlgebraDialect, "exec.ring_point", [OpRingPoint]>;
def RingRowsOp : BoundOp<AlgebraDialect, "exec.ring_rows", [OpRingRows]>;
def RingCoefficientsOp : BoundOp<AlgebraDialect, "exec.ring_coefficients", [OpRingCoefficients]>;
def RingAffineSumOp : BoundOp<AlgebraDialect, "exec.ring_affine_sum", [OpRingAffineSum]>;

def MatrixMulVectorOp : BoundOp<AlgebraDialect, "exec.matrix_mul_vector", [OpMatrixMulVector]>;

def MatrixDimensionOp : BoundOp<AlgebraDialect, "exec.matrix_dimension", [OpMatrixDimension]>;
def MatrixGetOp : BoundOp<AlgebraDialect, "exec.matrix_get", [OpMatrixGet]>;
def MatrixRowDotOp : BoundOp<AlgebraDialect, "exec.matrix_row_dot", [OpMatrixRowDot]>;
def MatrixColumnDotOp : BoundOp<AlgebraDialect, "exec.matrix_column_dot", [OpMatrixColumnDot]>;

def MatrixShapeCheckOp : BoundOp<AlgebraDialect, "exec.matrix_shape_check", [OpMatrixShapeCheck]>;

def MatrixTransposeMulVectorOp : BoundOp<AlgebraDialect, "exec.matrix_transpose_mul_vector", [OpMatrixTransposeMulVector]>;

def FieldNegateOp : BoundOp<AlgebraDialect, "exec.field_negate", [OpFieldNeg]>;

def PairingCheckOp : BoundOp<AlgebraDialect, "exec.pairing_check", [OpPairingCheck]>;

def FieldProductOp : BoundOp<AlgebraDialect, "exec.field_multiply", [OpFieldMul]>;

def FieldSubtractOp : BoundOp<AlgebraDialect, "exec.field_subtract", [OpFieldSub]>;

def FieldSumOp : BoundOp<AlgebraDialect, "exec.field_add", [OpFieldAdd]>;

def VectorAddOp : BoundOp<AlgebraDialect, "exec.vector_add", [OpVectorAdd]>;

def VectorAppendOp : BoundOp<AlgebraDialect, "exec.vector_append", [OpVectorAppend]>;

def VectorAtOp : BoundOp<AlgebraDialect, "exec.vector_at", [OpVectorAt]>;

def VectorConcatOp : BoundOp<AlgebraDialect, "exec.vector_concat", [OpVectorConcat]>;

def VectorConstantOp : BoundOp<AlgebraDialect, "exec.vector_constant", [OpVectorConstant]>;

def VectorDotOp : BoundOp<AlgebraDialect, "exec.vector_dot", [OpVectorDot], [DeclareOpInterfaceMethods<DiagonalContractionInterface>]>;

def VectorEmbedOp : BoundOp<AlgebraDialect, "exec.vector_embed", [OpVectorEmbed]>;

def VectorEmptyOp : BoundOp<AlgebraDialect, "exec.vector_empty", [OpVectorEmpty]>;

def VectorFillOp : BoundOp<AlgebraDialect, "exec.vector_fill", [OpVectorFill]>;

def VectorGatherOp : BoundOp<AlgebraDialect, "exec.vector_gather", [OpVectorGather]>;

def VectorGeometricOp : BoundOp<AlgebraDialect, "exec.vector_geometric", [OpVectorGeometric]>;

def VectorGetOp : BoundOp<AlgebraDialect, "exec.vector_get", [OpVectorGet]>;

def VectorInterleaveOp : BoundOp<AlgebraDialect, "exec.vector_interleave", [OpVectorInterleave]>;

def VectorInverseOp : BoundOp<AlgebraDialect, "exec.vector_inverse", [OpVectorInverse]>;

def VectorKroneckerOp : BoundOp<AlgebraDialect, "exec.vector_kronecker", [OpVectorKronecker]>;

def VectorLengthOp : BoundOp<AlgebraDialect, "exec.vector_length", [OpVectorLength]>;

def VectorLengthCheckOp : BoundOp<AlgebraDialect, "exec.vector_length_check", [OpVectorLengthCheck]>;

def VectorMatvecOp : BoundOp<AlgebraDialect, "exec.vector_matvec", [OpVectorMatvec]>;

def VectorMulOp : BoundOp<AlgebraDialect, "exec.vector_mul", [OpVectorMul], [DeclareOpInterfaceMethods<DiagonalProducerInterface>]>;

def VectorPowersOp : BoundOp<AlgebraDialect, "exec.vector_powers", [OpVectorPowers]>;

def VectorPrefixProductOp : BoundOp<AlgebraDialect, "exec.vector_prefix_product", [OpVectorPrefixProduct]>;

def VectorPrefixSumOp : BoundOp<AlgebraDialect, "exec.vector_prefix_sum", [OpVectorPrefixSum]>;

def VectorRotateOp : BoundOp<AlgebraDialect, "exec.vector_rotate", [OpVectorRotate]>;
def VectorBitReverseOp : BoundOp<AlgebraDialect, "exec.vector_bit_reverse", [OpVectorBitReverse]>;
def VectorBitReverseRowsOp : BoundOp<AlgebraDialect, "exec.vector_bit_reverse_rows", [OpVectorBitReverseRows]>;

def VectorScaleOp : BoundOp<AlgebraDialect, "exec.vector_scale", [OpVectorScale]>;

def VectorScatterSumOp : BoundOp<AlgebraDialect, "exec.vector_scatter_sum", [OpVectorScatterSum]>;

def VectorTransposeOp : BoundOp<AlgebraDialect, "exec.vector_transpose", [OpVectorTranspose]>;

def VectorSliceOp : BoundOp<AlgebraDialect, "exec.vector_slice", [OpVectorSlice]>;

def VectorSplatOp : BoundOp<AlgebraDialect, "exec.vector_splat", [OpVectorSplat]>;

def VectorSplitOp : BoundOp<AlgebraDialect, "exec.vector_split", [OpVectorSplit]>;

def VectorSubOp : BoundOp<AlgebraDialect, "exec.vector_sub", [OpVectorSub]>;

def VectorSumOp : BoundOp<AlgebraDialect, "exec.vector_sum", [OpVectorSum]>;
def VectorProductOp : BoundOp<AlgebraDialect, "exec.vector_product", [OpVectorProduct]>;

def BooleanAndOp : BoundOp<AlgebraDialect, "exec.bool_and", [OpBoolAnd]>;

def BooleanNotOp : BoundOp<AlgebraDialect, "exec.bool_not", [OpBoolNot]>;

def BooleanOrOp : BoundOp<AlgebraDialect, "exec.bool_or", [OpBoolOr]>;

def ConstantFieldOp : Op<AlgebraDialect, "constant",
                        [Pure, DeclareOpInterfaceMethods<MathematicalOpInterface>]> {
  let arguments = (ins StrAttr:$value);
  let results = (outs Field:$result);
  let hasVerifier = 1;
}
def ArrayFromElementsOp : Op<AlgebraDialect, "array_from_elements",
    [Pure, DeclareOpInterfaceMethods<MathematicalOpInterface>]> {
  let summary = "Pack ordered field elements into an exact nominal field array";
  let arguments = (ins Variadic<Field>:$elements);
  let results = (outs FieldArray:$result);
  let hasVerifier = 1;
}
def ArrayAtOp : Op<AlgebraDialect, "array_at",
                  [Pure, DeclareOpInterfaceMethods<MathematicalOpInterface>]> {
  let arguments = (ins FieldArray:$array, I64Attr:$index);
  let results = (outs Field:$result);
  let hasVerifier = 1;
  let hasFolder = 1;
}
def SubtractFieldOp : TotalMathOp<AlgebraDialect, "field_subtract", Field,
    Field, Field, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;

def FieldArrayFromVectorOp : BoundOp<AlgebraDialect, "exec.field_array_from_vector",
                                    [OpFieldArrayFromVector]>;
def FieldArrayAtOp : BoundOp<AlgebraDialect, "exec.field_array_at", [OpFieldArrayAt]>;
def FieldArrayGetOp : BoundOp<AlgebraDialect, "exec.field_array_get", [OpFieldArrayGet]>;


def PairingOp : TotalMathOp<AlgebraDialect, "pairing", Group, Group, Group, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;
def PairingApplyOp : BoundOp<AlgebraDialect, "exec.pairing", [OpPairingApply]>;
def VectorEqualOp : BoundOp<AlgebraDialect, "exec.vector_equal", [OpVectorEqual]>;
def VectorFindLastOp : BoundOp<AlgebraDialect, "exec.vector_find_last", [OpVectorFindLast]>;

class AlgebraFiniteOp<string name> : Op<AlgebraDialect, name,
    [Pure, DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins Variadic<AnyType>:$inputs, FlatSymbolRefAttr:$domain,
    OptionalAttr<FlatSymbolRefAttr>:$step, OptionalAttr<FlatSymbolRefAttr>:$body,
    OptionalAttr<FlatSymbolRefAttr>:$predicate);
  let results = (outs Variadic<AnyType>:$outputs);
  let hasVerifier = 1;
}
def FiniteFoldOp : AlgebraFiniteOp<"finite_fold">;
def FiniteCollectOp : AlgebraFiniteOp<"finite_collect">;

// A checked pointwise application of an existing private scalar helper over
// runtime vectors. `rowwise[i]` selects whether input i is a whole vector of
// the helper's scalar field (one row per element) or a scalar broadcast to
// every row. Ordered local.apply calls retain this declaration until numerical
// selection chooses and checks their actual Local payload. It is a
// checked bulk operation: shapes are compared before arithmetic, so it has no
// totality or purity contract. Algebra owns its formula vocabulary.
def MapRealizeOp : Op<AlgebraDialect, "map_realize",
    [Symbol, DeclareOpInterfaceMethods<SymbolUserOpInterface>,
     PreparationCallableOpInterface]> {
  let arguments = (ins SymbolNameAttr:$sym_name, FlatSymbolRefAttr:$helper,
    TypeAttrOf<FunctionType>:$function_type, DenseBoolArrayAttr:$rowwise);
  let assemblyFormat =
    "$sym_name `=` $helper $rowwise attr-dict `:` $function_type";
  let hasVerifier = 1;
}

#endif
