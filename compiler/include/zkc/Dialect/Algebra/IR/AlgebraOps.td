#ifndef ZKC_DIALECT_ALGEBRA_IR_ALGEBRAOPS_TD
#define ZKC_DIALECT_ALGEBRA_IR_ALGEBRAOPS_TD

include "zkc/Dialect/Types.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "zkc/Dialect/Kernels.td"
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

def FieldCompareOp : KernelOp<AlgebraDialect, "exec.field_equal", [OpFieldEqual]>;

def FieldConstantOp : KernelOp<AlgebraDialect, "exec.field_constant", [OpFieldConstant]>;

def CurveAddOp : KernelOp<AlgebraDialect, "exec.group_add", [OpCurveAdd]>;

def CurveAppendOp : KernelOp<AlgebraDialect, "exec.group_append", [OpCurveAppend]>;

def CurveAtOp : KernelOp<AlgebraDialect, "exec.group_at", [OpCurveAt]>;

def CurveConcatOp : KernelOp<AlgebraDialect, "exec.group_concat", [OpCurveConcat]>;

def CurveEmptyOp : KernelOp<AlgebraDialect, "exec.group_empty", [OpCurveEmpty]>;

def CurveEqualOp : KernelOp<AlgebraDialect, "exec.group_equal", [OpCurveEqual]>;

def CurveGeneratorOp : KernelOp<AlgebraDialect, "exec.group_generator", [OpCurveGenerator]>;

def CurveGetOp : KernelOp<AlgebraDialect, "exec.group_get", [OpCurveGet]>;

def CurveLengthOp : KernelOp<AlgebraDialect, "exec.group_length", [OpCurveLength]>;

def CurveMSMOp : KernelOp<AlgebraDialect, "exec.group_msm", [OpCurveMsm], [DeclareOpInterfaceMethods<DiagonalContractionInterface>]>;

def CurveNegateOp : KernelOp<AlgebraDialect, "exec.group_negate", [OpCurveNeg]>;

def CurveNonidentityOp : KernelOp<AlgebraDialect, "exec.group_nonidentity", [OpCurveNonidentity]>;

def CurveScaleOp : KernelOp<AlgebraDialect, "exec.group_scale", [OpCurveScale]>;

def CurveScaleEachOp : KernelOp<AlgebraDialect, "exec.group_scale_each", [OpCurveScaleEach], [DeclareOpInterfaceMethods<DiagonalProducerInterface>]>;

def CurveSplitOp : KernelOp<AlgebraDialect, "exec.group_split", [OpCurveSplit]>;

def CurveVectorAddOp : KernelOp<AlgebraDialect, "exec.group_vector_add", [OpCurveVectorAdd]>;

def CurveVectorScaleOp : KernelOp<AlgebraDialect, "exec.group_vector_scale", [OpCurveVectorScale]>;

def FieldEmbedOp : KernelOp<AlgebraDialect, "exec.field_embed", [OpFieldEmbed]>;

def FieldAddOp : TotalMathOp<AlgebraDialect, "field_add", Field, Field, Field, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;

def FieldEqualOp : TotalMathOp<AlgebraDialect, "field_equal", Field, Field, I1, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;

def FieldFromIndexOp : KernelOp<AlgebraDialect, "exec.field_from_index", [OpFieldFromIndex]>;

def FieldMultiplyOp : TotalMathOp<AlgebraDialect, "field_multiply", Field, Field, Field, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;

def FixedVectorDotOp : KernelOp<AlgebraDialect, "exec.fixed_vector_dot",
                              [OpFixedVectorDot]>;

def FixedVectorFromVectorOp : KernelOp<AlgebraDialect, "exec.fixed_vector_from_vector",
                                     [OpFixedVectorFromVector]>;

def FixedVectorToVectorOp : KernelOp<AlgebraDialect, "exec.fixed_vector_to_vector",
                                   [OpFixedVectorToVector]>;

def GroupAddOp : TotalMathOp<AlgebraDialect, "group_add", Group, Group, Group, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;

def GroupEqualOp : TotalMathOp<AlgebraDialect, "group_equal", Group, Group, I1, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;

def GroupScaleOp : TotalMathOp<AlgebraDialect, "group_scale", Group, Field, Group, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;

def IndexAddOp : KernelOp<AlgebraDialect, "exec.index_add", [OpIndexAdd]>;

def IndexConstantOp : KernelOp<AlgebraDialect, "exec.index_constant", [OpIndexConstant]>;

def IndexDivOp : KernelOp<AlgebraDialect, "exec.index_div", [OpIndexDiv]>;

def IndexEqualOp : KernelOp<AlgebraDialect, "exec.index_equal", [OpIndexEqual]>;

def IndexLessOp : KernelOp<AlgebraDialect, "exec.index_less", [OpIndexLess]>;

def IndexModOp : KernelOp<AlgebraDialect, "exec.index_mod", [OpIndexMod]>;

def IndexMulOp : KernelOp<AlgebraDialect, "exec.index_mul", [OpIndexMul]>;

def IndexSubOp : KernelOp<AlgebraDialect, "exec.index_sub", [OpIndexSub]>;

def IndicesAppendOp : KernelOp<AlgebraDialect, "exec.indices_append", [OpIndicesAppend]>;

def IndicesAtOp : KernelOp<AlgebraDialect, "exec.indices_at", [OpIndicesAt]>;

def IndicesEmptyOp : KernelOp<AlgebraDialect, "exec.indices_empty", [OpIndicesEmpty]>;

def IndicesLengthOp : KernelOp<AlgebraDialect, "exec.indices_length", [OpIndicesLength]>;

def FieldInverseOp : KernelOp<AlgebraDialect, "exec.field_inverse", [OpFieldInverse]>;

def MatrixBilinearOp : KernelOp<AlgebraDialect, "exec.matrix_bilinear", [OpMatrixBilinear]>;

def MatrixIdentityCheckOp : KernelOp<AlgebraDialect, "exec.matrix_identity_check", [OpMatrixIdentityCheck]>;

def RingPointOp : KernelOp<AlgebraDialect, "exec.ring_point", [OpRingPoint]>;
def RingRowsOp : KernelOp<AlgebraDialect, "exec.ring_rows", [OpRingRows]>;
def RingCoefficientsOp : KernelOp<AlgebraDialect, "exec.ring_coefficients", [OpRingCoefficients]>;
def RingAffineSumOp : KernelOp<AlgebraDialect, "exec.ring_affine_sum", [OpRingAffineSum]>;

def MatrixMulVectorOp : KernelOp<AlgebraDialect, "exec.matrix_mul_vector", [OpMatrixMulVector]>;

def MatrixDimensionOp : KernelOp<AlgebraDialect, "exec.matrix_dimension", [OpMatrixDimension]>;

def MatrixShapeCheckOp : KernelOp<AlgebraDialect, "exec.matrix_shape_check", [OpMatrixShapeCheck]>;

def MatrixTransposeMulVectorOp : KernelOp<AlgebraDialect, "exec.matrix_transpose_mul_vector", [OpMatrixTransposeMulVector]>;

def FieldNegateOp : KernelOp<AlgebraDialect, "exec.field_negate", [OpFieldNeg]>;

def PairingCheckOp : KernelOp<AlgebraDialect, "exec.pairing_check", [OpPairingCheck]>;

def FieldProductOp : KernelOp<AlgebraDialect, "exec.field_multiply", [OpFieldMul]>;

def FieldSubtractOp : KernelOp<AlgebraDialect, "exec.field_subtract", [OpFieldSub]>;

def FieldSumOp : KernelOp<AlgebraDialect, "exec.field_add", [OpFieldAdd]>;

def VectorAddOp : KernelOp<AlgebraDialect, "exec.vector_add", [OpVectorAdd]>;

def VectorAppendOp : KernelOp<AlgebraDialect, "exec.vector_append", [OpVectorAppend]>;

def VectorAtOp : KernelOp<AlgebraDialect, "exec.vector_at", [OpVectorAt]>;

def VectorConcatOp : KernelOp<AlgebraDialect, "exec.vector_concat", [OpVectorConcat]>;

def VectorConstantOp : KernelOp<AlgebraDialect, "exec.vector_constant", [OpVectorConstant]>;

def VectorDotOp : KernelOp<AlgebraDialect, "exec.vector_dot", [OpVectorDot], [DeclareOpInterfaceMethods<DiagonalContractionInterface>]>;

def VectorEmbedOp : KernelOp<AlgebraDialect, "exec.vector_embed", [OpVectorEmbed]>;

def VectorEmptyOp : KernelOp<AlgebraDialect, "exec.vector_empty", [OpVectorEmpty]>;

def VectorFillOp : KernelOp<AlgebraDialect, "exec.vector_fill", [OpVectorFill]>;

def VectorGatherOp : KernelOp<AlgebraDialect, "exec.vector_gather", [OpVectorGather]>;

def VectorGeometricOp : KernelOp<AlgebraDialect, "exec.vector_geometric", [OpVectorGeometric]>;

def VectorGetOp : KernelOp<AlgebraDialect, "exec.vector_get", [OpVectorGet]>;

def VectorInterleaveOp : KernelOp<AlgebraDialect, "exec.vector_interleave", [OpVectorInterleave]>;

def VectorInverseOp : KernelOp<AlgebraDialect, "exec.vector_inverse", [OpVectorInverse]>;

def VectorKroneckerOp : KernelOp<AlgebraDialect, "exec.vector_kronecker", [OpVectorKronecker]>;

def VectorLengthOp : KernelOp<AlgebraDialect, "exec.vector_length", [OpVectorLength]>;

def VectorLengthCheckOp : KernelOp<AlgebraDialect, "exec.vector_length_check", [OpVectorLengthCheck]>;

def VectorMatvecOp : KernelOp<AlgebraDialect, "exec.vector_matvec", [OpVectorMatvec]>;

def VectorMulOp : KernelOp<AlgebraDialect, "exec.vector_mul", [OpVectorMul], [DeclareOpInterfaceMethods<DiagonalProducerInterface>]>;

def VectorPowersOp : KernelOp<AlgebraDialect, "exec.vector_powers", [OpVectorPowers]>;

def VectorPrefixProductOp : KernelOp<AlgebraDialect, "exec.vector_prefix_product", [OpVectorPrefixProduct]>;

def VectorPrefixSumOp : KernelOp<AlgebraDialect, "exec.vector_prefix_sum", [OpVectorPrefixSum]>;

def VectorRotateOp : KernelOp<AlgebraDialect, "exec.vector_rotate", [OpVectorRotate]>;

def VectorScaleOp : KernelOp<AlgebraDialect, "exec.vector_scale", [OpVectorScale]>;

def VectorScatterSumOp : KernelOp<AlgebraDialect, "exec.vector_scatter_sum", [OpVectorScatterSum]>;

def VectorTransposeOp : KernelOp<AlgebraDialect, "exec.vector_transpose", [OpVectorTranspose]>;

def VectorSliceOp : KernelOp<AlgebraDialect, "exec.vector_slice", [OpVectorSlice]>;

def VectorSplatOp : KernelOp<AlgebraDialect, "exec.vector_splat", [OpVectorSplat]>;

def VectorSplitOp : KernelOp<AlgebraDialect, "exec.vector_split", [OpVectorSplit]>;

def VectorSubOp : KernelOp<AlgebraDialect, "exec.vector_sub", [OpVectorSub]>;

def VectorSumOp : KernelOp<AlgebraDialect, "exec.vector_sum", [OpVectorSum]>;

def BooleanAndOp : KernelOp<AlgebraDialect, "exec.bool_and", [OpBoolAnd]>;

def BooleanNotOp : KernelOp<AlgebraDialect, "exec.bool_not", [OpBoolNot]>;

def BooleanOrOp : KernelOp<AlgebraDialect, "exec.bool_or", [OpBoolOr]>;

def ConstantFieldOp : Op<AlgebraDialect, "constant",
                        [Pure, DeclareOpInterfaceMethods<MathematicalOpInterface>]> {
  let arguments = (ins StrAttr:$value);
  let results = (outs Field:$result);
  let hasVerifier = 1;
}
def ArrayAtOp : Op<AlgebraDialect, "array_at",
                  [Pure, DeclareOpInterfaceMethods<MathematicalOpInterface>]> {
  let arguments = (ins AnyRankedTensor:$array, I64Attr:$index);
  let results = (outs Field:$result);
  let hasVerifier = 1;
}
def SubtractFieldOp : TotalMathOp<AlgebraDialect, "field_subtract", Field,
    Field, Field, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;

def FieldArrayFromVectorOp : KernelOp<AlgebraDialect, "exec.field_array_from_vector",
                                    [OpFieldArrayFromVector]>;
def FieldArrayAtOp : KernelOp<AlgebraDialect, "exec.field_array_at", [OpFieldArrayAt]>;


def PairingOp : TotalMathOp<AlgebraDialect, "pairing", Group, Group, Group, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;
def PairingApplyOp : KernelOp<AlgebraDialect, "exec.pairing", [OpPairingApply]>;
def VectorEqualOp : KernelOp<AlgebraDialect, "exec.vector_equal", [OpVectorEqual]>;

// A checked pointwise application of an existing private scalar helper over
// runtime vectors. `rowwise[i]` selects whether input i is a whole vector of
// the helper's scalar field (one row per element) or a scalar broadcast to
// every row. The declaration is called by local.apply and is replaced during
// preparation by an ordinary local.func with the same signature. It is a
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
