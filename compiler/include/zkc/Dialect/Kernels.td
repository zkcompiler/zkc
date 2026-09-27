#ifndef ZKC_DIALECT_KERNELS_TD
#define ZKC_DIALECT_KERNELS_TD
include "zkc/Dialect/Constraints.td"
include "zkc/Contracts/Declarations.td"
include "zkc/Interfaces/LinearContraction.td"
// These mathematical operations retain potential failure: no Pure/speculatable
// marker is inferred merely from a mathematical totality claim. The installed
// verifier checks types, attributes and physical selection. Semantic facets
// live in Contracts/Operations.h; absent facets grant no rewrite permission.
class KernelOp<Dialect dialect, string name, list<ZKC_Operation> declarations,
               list<Trait> traits = []>
    : Op<dialect, name, traits>, ZKC_ContractMapping {
  let contracts = declarations;
  let arguments = (ins Variadic<Zkc_ProtocolData>:$inputs, StrAttr:$site,
    ArrayAttr:$parameters, OptionalAttr<FlatSymbolRefAttr>:$binding);
  let results = (outs Variadic<Zkc_ProtocolData>:$outputs);
  let hasVerifier = 1;
  let extraClassDefinition = [{
    ::llvm::LogicalResult $cppClass::verify() {
      return ::zkc::detail::verifyLogicalKernel(getOperation());
    }
  }];
}
def ResourceUnitCreateOp : KernelOp<PIRDialect, "resource_unit_create", [OpResourceUnitCreate]> {
  let description = [{
    Creates one zero-payload logical resource unit of the slot named by the
    binding. The unit is affine: it can be passed or consumed once and is
    retired with its frame when neither returned nor consumed (docs/spec/domains/values.md).
  }];
}
def ResourceUnitPassOp : KernelOp<PIRDialect, "resource_unit_pass", [OpResourceUnitPass]> {
  let description = [{
    Moves a resource unit into a fresh occurrence of the same slot. The input
    occurrence is consumed; the operation grants no copy (docs/spec/domains/values.md).
  }];
}
def ResourceUnitConsumeOp : KernelOp<PIRDialect, "resource_unit_consume", [OpResourceUnitConsume]> {
  let description = [{
    Consumes a resource unit and produces nothing. It must remain even though
    it has no result, since removing it would change the unit's lifetime and the
    observed operation sequence (docs/spec/domains/values.md).
  }];
}
def OracleCommitOp : KernelOp<OracleDialect, "commit", [OpOracleCommit]>;
def FixedVectorFromVectorOp : KernelOp<AlgebraDialect, "fixed_vector_from_vector",
                                     [OpFixedVectorFromVector]>;
def FixedVectorToVectorOp : KernelOp<AlgebraDialect, "fixed_vector_to_vector",
                                   [OpFixedVectorToVector]>;
def FixedVectorDotOp : KernelOp<AlgebraDialect, "fixed_vector_dot",
                              [OpFixedVectorDot]>;
def OracleOpenOp : KernelOp<OracleDialect, "open", [OpOracleOpen]>;
def OracleCheckOp : KernelOp<OracleDialect, "check", [OpOracleCheck]>;
def CommitmentsEmptyOp : KernelOp<OracleDialect, "commitments_empty", [OpCommitmentsEmpty]>;
def CommitmentsAppendOp : KernelOp<OracleDialect, "commitments_append", [OpCommitmentsAppend]>;
def CommitmentsAtOp : KernelOp<OracleDialect, "commitments_at", [OpCommitmentsAt]>;
def CommitmentsLengthOp : KernelOp<OracleDialect, "commitments_length", [OpCommitmentsLength]>;
def OpeningStatesEmptyOp : KernelOp<OracleDialect, "opening_states_empty", [OpOpeningStatesEmpty]>;
def OpeningStatesAppendOp : KernelOp<OracleDialect, "opening_states_append", [OpOpeningStatesAppend]>;
def OpeningStatesAtOp : KernelOp<OracleDialect, "opening_states_at", [OpOpeningStatesAt]>;
def OpeningStatesLengthOp : KernelOp<OracleDialect, "opening_states_length", [OpOpeningStatesLength]>;
def ExternalMoneroInitOp : KernelOp<AlgebraDialect, "external_monero_init", [OpExternalMoneroInit]> {
  let description = [{
    Starts the pinned Monero scalar hash chain from its initial bytes.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalMoneroHashOp : KernelOp<AlgebraDialect, "external_monero_hash", [OpExternalMoneroHash]> {
  let description = [{
    Hashes concatenated words to Monero scalar bytes without a chain state.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalMoneroUpdateOp : KernelOp<AlgebraDialect, "external_monero_update", [OpExternalMoneroUpdate]> {
  let description = [{
    Absorbs concatenated words into the Monero hash chain; returns the successor state and the derived scalar bytes.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalOpenvmInitOp : KernelOp<AlgebraDialect, "external_openvm_init", [OpExternalOpenvmInit]> {
  let description = [{
    Starts the pinned OpenVM BabyBear Poseidon2 duplex state.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalOpenvmObserveOp : KernelOp<AlgebraDialect, "external_openvm_observe", [OpExternalOpenvmObserve]> {
  let description = [{
    Absorbs field words into the OpenVM duplex; returns the successor state.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalOpenvmSampleOp : KernelOp<AlgebraDialect, "external_openvm_sample", [OpExternalOpenvmSample]> {
  let description = [{
    Squeezes one base-field sample from the OpenVM duplex.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalOpenvmSampleExtOp : KernelOp<AlgebraDialect, "external_openvm_sample_ext", [OpExternalOpenvmSampleExt]> {
  let description = [{
    Squeezes the four coefficients of one quartic-extension sample.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalOpenvmSampleBitsOp : KernelOp<AlgebraDialect, "external_openvm_sample_bits", [OpExternalOpenvmSampleBits]> {
  let description = [{
    Squeezes a sample and masks it to the requested number of bits, as the pinned query sampler does.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalOpenvmCheckWitnessOp : KernelOp<AlgebraDialect, "external_openvm_check_witness", [OpExternalOpenvmCheckWitness]> {
  let description = [{
    Checks a grinding witness against the requested number of bits on the live state.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def IndexConstantOp : KernelOp<AlgebraDialect, "index_constant", [OpIndexConstant]>;
def IndexAddOp : KernelOp<AlgebraDialect, "index_add", [OpIndexAdd]>;
def IndexSubOp : KernelOp<AlgebraDialect, "index_sub", [OpIndexSub]>;
def IndexMulOp : KernelOp<AlgebraDialect, "index_mul", [OpIndexMul]>;
def IndexDivOp : KernelOp<AlgebraDialect, "index_div", [OpIndexDiv]>;
def IndexModOp : KernelOp<AlgebraDialect, "index_mod", [OpIndexMod]>;
def IndexEqualOp : KernelOp<AlgebraDialect, "index_equal", [OpIndexEqual]>;
def IndexLessOp : KernelOp<AlgebraDialect, "index_less", [OpIndexLess]>;
def IndicesEmptyOp : KernelOp<AlgebraDialect, "indices_empty", [OpIndicesEmpty]>;
def IndicesAppendOp : KernelOp<AlgebraDialect, "indices_append", [OpIndicesAppend]>;
def IndicesAtOp : KernelOp<AlgebraDialect, "indices_at", [OpIndicesAt]>;
def IndicesLengthOp : KernelOp<AlgebraDialect, "indices_length", [OpIndicesLength]>;
def VectorGetOp : KernelOp<AlgebraDialect, "vector_get", [OpVectorGet]>;
def VectorSliceOp : KernelOp<AlgebraDialect, "vector_slice", [OpVectorSlice]>;
def VectorLengthOp : KernelOp<AlgebraDialect, "vector_length", [OpVectorLength]>;
def VectorRotateOp : KernelOp<AlgebraDialect, "vector_rotate", [OpVectorRotate]>;
def VectorInterleaveOp : KernelOp<AlgebraDialect, "vector_interleave", [OpVectorInterleave]>;
def VectorPrefixProductOp : KernelOp<AlgebraDialect, "vector_prefix_product", [OpVectorPrefixProduct]>;
def VectorPrefixSumOp : KernelOp<AlgebraDialect, "vector_prefix_sum", [OpVectorPrefixSum]>;
def VectorInverseOp : KernelOp<AlgebraDialect, "vector_inverse", [OpVectorInverse]>;
def VectorEmbedOp : KernelOp<AlgebraDialect, "vector_embed", [OpVectorEmbed]>;
def VectorFillOp : KernelOp<AlgebraDialect, "vector_fill", [OpVectorFill]>;
def VectorGeometricOp : KernelOp<AlgebraDialect, "vector_geometric", [OpVectorGeometric]>;
def FieldFromIndexOp : KernelOp<AlgebraDialect, "field_from_index", [OpFieldFromIndex]>;
def CoefficientCountOp : KernelOp<PolynomialDialect, "coefficient_count", [OpPolyCoefficientCount]>;
def CosetEvaluateOp : KernelOp<PolynomialDialect, "coset_evaluate", [OpPolyCosetEvaluate]>;
def CosetInterpolateOp : KernelOp<PolynomialDialect, "coset_interpolate", [OpPolyCosetInterpolate]>;
def DomainPointOp : KernelOp<PolynomialDialect, "domain_point", [OpPolyDomainPoint]>;
def DomainRootOp : KernelOp<PolynomialDialect, "domain_root", [OpPolyDomainRoot]>;
def DomainPointsOp : KernelOp<PolynomialDialect, "domain_points", [OpPolyDomainPoints]>;
def EvenOddFoldOp : KernelOp<PolynomialDialect, "even_odd_fold", [OpPolyEvenOddFold]>;
def DivideOpeningOp : KernelOp<PolynomialDialect, "divide_opening", [OpPolyDivideOpening]>;
def OpeningQuotientOp : KernelOp<PolynomialDialect, "opening_quotient", [OpPolyOpeningQuotient]>;
def FieldSubtractOp : KernelOp<AlgebraDialect, "subtract", [OpFieldSub]>;
def FieldNegateOp : KernelOp<AlgebraDialect, "negate", [OpFieldNeg]>;
def FieldInverseOp : KernelOp<AlgebraDialect, "inverse", [OpFieldInverse]>;
def FieldEmbedOp : KernelOp<AlgebraDialect, "embed", [OpFieldEmbed]>;
def MatrixMulVectorOp : KernelOp<AlgebraDialect, "matrix_mul_vector", [OpMatrixMulVector]>;
def MatrixTransposeMulVectorOp : KernelOp<AlgebraDialect, "matrix_transpose_mul_vector", [OpMatrixTransposeMulVector]>;
def MatrixBilinearOp : KernelOp<AlgebraDialect, "matrix_bilinear", [OpMatrixBilinear]>;
def MatrixShapeCheckOp : KernelOp<AlgebraDialect, "matrix_shape_check", [OpMatrixShapeCheck]>;
def MatrixIdentityCheckOp : KernelOp<AlgebraDialect, "matrix_identity_check", [OpMatrixIdentityCheck]>;
def VectorConstantOp : KernelOp<AlgebraDialect, "vector_constant", [OpVectorConstant]>;
def VectorScatterSumOp : KernelOp<AlgebraDialect, "vector_scatter_sum", [OpVectorScatterSum]>;
def VectorEmptyOp : KernelOp<AlgebraDialect, "vector_empty", [OpVectorEmpty]>;
def VectorAppendOp : KernelOp<AlgebraDialect, "vector_append", [OpVectorAppend]>;
def VectorSplatOp : KernelOp<AlgebraDialect, "vector_splat", [OpVectorSplat]>;
def VectorPowersOp : KernelOp<AlgebraDialect, "vector_powers", [OpVectorPowers]>;
def VectorAddOp : KernelOp<AlgebraDialect, "vector_add", [OpVectorAdd]>;
def VectorSubOp : KernelOp<AlgebraDialect, "vector_sub", [OpVectorSub]>;
def VectorMulOp : KernelOp<AlgebraDialect, "vector_mul", [OpVectorMul], [DeclareOpInterfaceMethods<DiagonalProducerInterface>]>;
def VectorDotOp : KernelOp<AlgebraDialect, "vector_dot", [OpVectorDot], [DeclareOpInterfaceMethods<DiagonalContractionInterface>]>;
def VectorConcatOp : KernelOp<AlgebraDialect, "vector_concat", [OpVectorConcat]>;
def VectorKroneckerOp : KernelOp<AlgebraDialect, "vector_kronecker", [OpVectorKronecker]>;
def VectorMatvecOp : KernelOp<AlgebraDialect, "vector_matvec", [OpVectorMatvec]>;
def VectorScaleOp : KernelOp<AlgebraDialect, "vector_scale", [OpVectorScale]>;
def VectorSumOp : KernelOp<AlgebraDialect, "vector_sum", [OpVectorSum]>;
def VectorSplitOp : KernelOp<AlgebraDialect, "vector_split", [OpVectorSplit]>;
def VectorAtOp : KernelOp<AlgebraDialect, "vector_at", [OpVectorAt]>;
def VectorLengthCheckOp : KernelOp<AlgebraDialect, "vector_length_check", [OpVectorLengthCheck]>;
def VectorGatherOp : KernelOp<AlgebraDialect, "vector_gather", [OpVectorGather]>;
def PointToVectorOp : KernelOp<PolynomialDialect, "point_to_vector", [OpVectorFromPoint]>;
def TableToVectorOp : KernelOp<PolynomialDialect, "table_to_vector", [OpVectorFromTable]>;
def PointFromVectorOp : KernelOp<PolynomialDialect, "point_from_vector", [OpVectorToPoint]>;
def TableFromVectorOp : KernelOp<PolynomialDialect, "table_from_vector", [OpVectorToTable]>;
def EqualityWeightsOp : KernelOp<PolynomialDialect, "equality_weights", [OpPolyEqualityWeights]>;
def FromCoefficientsOp : KernelOp<PolynomialDialect, "from_coefficients", [OpPolyFromCoefficients]>;
def CoefficientsOp : KernelOp<PolynomialDialect, "coefficients", [OpPolyCoefficients]>;
def DegreeCheckOp : KernelOp<PolynomialDialect, "degree_check", [OpPolyDegreeCheck]>;
def UnivariateEvaluateOp : KernelOp<PolynomialDialect, "univariate_evaluate", [OpPolyUnivariateEvaluate]>;
def UnivariateBoundaryOp : KernelOp<PolynomialDialect, "univariate_boundary", [OpPolyUnivariateBoundary]>;
def RandomVectorOp : KernelOp<PIRDialect, "random_vector", [OpRandomVector]>;
def CurveNegateOp : KernelOp<AlgebraDialect, "curve_negate", [OpCurveNeg]>;
def CurveNonidentityOp : KernelOp<AlgebraDialect, "curve_nonidentity", [OpCurveNonidentity]>;
def CurveMSMOp : KernelOp<AlgebraDialect, "curve_msm", [OpCurveMsm], [DeclareOpInterfaceMethods<DiagonalContractionInterface>]>;
def CurveScaleEachOp : KernelOp<AlgebraDialect, "curve_scale_each", [OpCurveScaleEach], [DeclareOpInterfaceMethods<DiagonalProducerInterface>]>;
def CurveVectorAddOp : KernelOp<AlgebraDialect, "curve_vector_add", [OpCurveVectorAdd]>;
def CurveVectorScaleOp : KernelOp<AlgebraDialect, "curve_vector_scale", [OpCurveVectorScale]>;
def CurveSplitOp : KernelOp<AlgebraDialect, "curve_split", [OpCurveSplit]>;
def CurveConcatOp : KernelOp<AlgebraDialect, "curve_concat", [OpCurveConcat]>;
// Ordered, equal-length G1/G2 vectors; returns whether the pairing product is
// one. Length mismatch is an operation failure, and the empty product is one.
// Nominal source groups are resolved independently by the binding signature.
def PairingCheckOp : KernelOp<AlgebraDialect, "pairing_check", [OpPairingCheck]>;

def FieldConstantOp : KernelOp<AlgebraDialect, "constant", [OpFieldConstant]>;
def FieldSumOp : KernelOp<AlgebraDialect, "sum", [OpFieldAdd]>;
def FieldProductOp : KernelOp<AlgebraDialect, "product", [OpFieldMul]>;
def FieldCompareOp : KernelOp<AlgebraDialect, "compare", [OpFieldEqual]>;
def BooleanAndOp : KernelOp<PIRDialect, "and", [OpBoolAnd]>;
def BooleanNotOp : KernelOp<PIRDialect, "not", [OpBoolNot]>;
def BooleanOrOp : KernelOp<PIRDialect, "or", [OpBoolOr]>;
def RequireOp : KernelOp<PIRDialect, "require", [OpControlRequire]>;
def ProductSumOp : KernelOp<PolynomialDialect, "product_sum", [OpPolyProductSum]>;
def ProductRoundOp : KernelOp<PolynomialDialect, "product_round", [OpPolyProductRound]>;
def BoundaryOp : KernelOp<PolynomialDialect, "boundary", [OpPolyBoundary]>;
def RoundEvaluateOp : KernelOp<PolynomialDialect, "round_evaluate", [OpPolyRoundEvaluate]>;
def FoldOp : KernelOp<PolynomialDialect, "fold", [OpPolyFold]>;
def MLEEvaluateOp : KernelOp<PolynomialDialect, "mle_evaluate", [OpPolyEvaluate]>;
def EmptyPointOp : KernelOp<PolynomialDialect, "empty_point", [OpPolyEmptyPoint]>;
def AppendPointOp : KernelOp<PolynomialDialect, "append_point", [OpPolyAppendPoint]>;
def PCSCommitOp : KernelOp<PCSDialect, "commit", [OpPcsCommit]>;
def PCSOpenOp : KernelOp<PCSDialect, "open", [OpPcsOpen]>;
def PCSCheckOp : KernelOp<PCSDialect, "check", [OpPcsCheck]>;
def RandomIndexOp : KernelOp<PIRDialect, "random_index", [OpRandomIndex]>;
def TranscriptDrawIndexOp : KernelOp<PIRDialect, "transcript_draw_index", [OpTranscriptDrawIndex]>;
def RandomDrawOp : KernelOp<PIRDialect, "random_draw", [OpRandomDraw]>;

def PCSEqualOp : KernelOp<PCSDialect, "equal", [OpPcsEqual]>;
def TranscriptObserveOp : KernelOp<PIRDialect, "transcript_observe", []> {
  // Payloads differ deliberately; each remains a distinct checked contract.
  let observationContracts = [
    OpTranscriptObserveBool, OpTranscriptObserveField, OpTranscriptObserveTable,
    OpTranscriptObservePoint, OpTranscriptObserveRound,
    OpTranscriptObserveCommitment, OpTranscriptObserveProof,
    OpTranscriptObserveGroup, OpTranscriptObserveGroups,
    OpTranscriptObserveMatrix, OpTranscriptObserveVector,
    OpTranscriptObservePolynomial, OpTranscriptObserveIndex,
    OpTranscriptObserveIndices, OpTranscriptObserveCommitments
  ];
}
def TranscriptChallengeOp : KernelOp<PIRDialect, "transcript_challenge", [OpTranscriptChallenge]>;
def CurveGeneratorOp : KernelOp<AlgebraDialect, "curve_generator", [OpCurveGenerator]>;
def CurveAddOp : KernelOp<AlgebraDialect, "curve_add", [OpCurveAdd]>;
def CurveScaleOp : KernelOp<AlgebraDialect, "curve_scale", [OpCurveScale]>;
def CurveEqualOp : KernelOp<AlgebraDialect, "curve_equal", [OpCurveEqual]>;
def CurveEmptyOp : KernelOp<AlgebraDialect, "curve_empty", [OpCurveEmpty]>;
def CurveAppendOp : KernelOp<AlgebraDialect, "curve_append", [OpCurveAppend]>;
def CurveAtOp : KernelOp<AlgebraDialect, "curve_at", [OpCurveAt]>;
def CurveGetOp : KernelOp<AlgebraDialect, "curve_get", [OpCurveGet]>;
def CurveLengthOp : KernelOp<AlgebraDialect, "curve_length", [OpCurveLength]>;
def CurveCommitOp : KernelOp<AlgebraDialect, "curve_commit", [OpCurveCommit]>;
def CurveResponseOp : KernelOp<AlgebraDialect, "curve_response", [OpCurveResponse]>;
#endif
