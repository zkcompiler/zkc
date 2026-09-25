#ifndef ZKC_DIALECT_KERNELS_TD
#define ZKC_DIALECT_KERNELS_TD
include "zkc/Dialect/Constraints.td"
include "zkc/Interfaces/LinearContraction.td"
// These mathematical operations retain potential failure: no Pure/speculatable
// marker is inferred merely from a mathematical totality claim. The installed
// verifier checks types, attributes and physical selection. Semantic facets
// live in Protocol/Contracts.h; absent facets grant no rewrite permission.
class KernelOp<Dialect dialect, string name, list<Trait> traits = []> : Op<dialect, name, traits> {
  let arguments = (ins Variadic<Zkc_ProtocolData>:$inputs, StrAttr:$site,
    ArrayAttr:$parameters, OptionalAttr<FlatSymbolRefAttr>:$binding);
  let results = (outs Variadic<Zkc_ProtocolData>:$outputs);
  let hasVerifier = 1;
}
def ResourceUnitCreateOp : KernelOp<PIRDialect, "resource_unit_create"> {
  let description = [{
    Creates one zero-payload logical resource unit of the slot named by the
    binding. The unit is affine: it can be passed or consumed once and is
    retired with its frame when neither returned nor consumed (docs/spec/domains/values.md).
  }];
}
def ResourceUnitPassOp : KernelOp<PIRDialect, "resource_unit_pass"> {
  let description = [{
    Moves a resource unit into a fresh occurrence of the same slot. The input
    occurrence is consumed; the operation grants no copy (docs/spec/domains/values.md).
  }];
}
def ResourceUnitConsumeOp : KernelOp<PIRDialect, "resource_unit_consume"> {
  let description = [{
    Consumes a resource unit and produces nothing. It must remain even though
    it has no result, since removing it would change the unit's lifetime and the
    observed operation sequence (docs/spec/domains/values.md).
  }];
}
def OracleCommitOp : KernelOp<OracleDialect, "commit">;
def OracleOpenOp : KernelOp<OracleDialect, "open">;
def OracleCheckOp : KernelOp<OracleDialect, "check">;
def CommitmentsEmptyOp : KernelOp<OracleDialect, "commitments_empty">;
def CommitmentsAppendOp : KernelOp<OracleDialect, "commitments_append">;
def CommitmentsAtOp : KernelOp<OracleDialect, "commitments_at">;
def CommitmentsLengthOp : KernelOp<OracleDialect, "commitments_length">;
def OpeningStatesEmptyOp : KernelOp<OracleDialect, "opening_states_empty">;
def OpeningStatesAppendOp : KernelOp<OracleDialect, "opening_states_append">;
def OpeningStatesAtOp : KernelOp<OracleDialect, "opening_states_at">;
def OpeningStatesLengthOp : KernelOp<OracleDialect, "opening_states_length">;
def ExternalMoneroInitOp : KernelOp<AlgebraDialect, "external_monero_init"> {
  let description = [{
    Starts the pinned Monero scalar hash chain from its initial bytes.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalMoneroHashOp : KernelOp<AlgebraDialect, "external_monero_hash"> {
  let description = [{
    Hashes concatenated words to Monero scalar bytes without a chain state.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalMoneroUpdateOp : KernelOp<AlgebraDialect, "external_monero_update"> {
  let description = [{
    Absorbs concatenated words into the Monero hash chain; returns the successor state and the derived scalar bytes.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalOpenvmInitOp : KernelOp<AlgebraDialect, "external_openvm_init"> {
  let description = [{
    Starts the pinned OpenVM BabyBear Poseidon2 duplex state.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalOpenvmObserveOp : KernelOp<AlgebraDialect, "external_openvm_observe"> {
  let description = [{
    Absorbs field words into the OpenVM duplex; returns the successor state.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalOpenvmSampleOp : KernelOp<AlgebraDialect, "external_openvm_sample"> {
  let description = [{
    Squeezes one base-field sample from the OpenVM duplex.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalOpenvmSampleExtOp : KernelOp<AlgebraDialect, "external_openvm_sample_ext"> {
  let description = [{
    Squeezes the four coefficients of one quartic-extension sample.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalOpenvmSampleBitsOp : KernelOp<AlgebraDialect, "external_openvm_sample_bits"> {
  let description = [{
    Squeezes a sample and masks it to the requested number of bits, as the pinned query sampler does.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalOpenvmCheckWitnessOp : KernelOp<AlgebraDialect, "external_openvm_check_witness"> {
  let description = [{
    Checks a grinding witness against the requested number of bits on the live state.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def IndexConstantOp : KernelOp<AlgebraDialect, "index_constant">;
def IndexAddOp : KernelOp<AlgebraDialect, "index_add">;
def IndexSubOp : KernelOp<AlgebraDialect, "index_sub">;
def IndexMulOp : KernelOp<AlgebraDialect, "index_mul">;
def IndexDivOp : KernelOp<AlgebraDialect, "index_div">;
def IndexModOp : KernelOp<AlgebraDialect, "index_mod">;
def IndexEqualOp : KernelOp<AlgebraDialect, "index_equal">;
def IndexLessOp : KernelOp<AlgebraDialect, "index_less">;
def IndicesEmptyOp : KernelOp<AlgebraDialect, "indices_empty">;
def IndicesAppendOp : KernelOp<AlgebraDialect, "indices_append">;
def IndicesAtOp : KernelOp<AlgebraDialect, "indices_at">;
def IndicesLengthOp : KernelOp<AlgebraDialect, "indices_length">;
def VectorGetOp : KernelOp<AlgebraDialect, "vector_get">;
def VectorSliceOp : KernelOp<AlgebraDialect, "vector_slice">;
def VectorLengthOp : KernelOp<AlgebraDialect, "vector_length">;
def VectorRotateOp : KernelOp<AlgebraDialect, "vector_rotate">;
def VectorInterleaveOp : KernelOp<AlgebraDialect, "vector_interleave">;
def VectorPrefixProductOp : KernelOp<AlgebraDialect, "vector_prefix_product">;
def VectorPrefixSumOp : KernelOp<AlgebraDialect, "vector_prefix_sum">;
def VectorInverseOp : KernelOp<AlgebraDialect, "vector_inverse">;
def VectorEmbedOp : KernelOp<AlgebraDialect, "vector_embed">;
def VectorFillOp : KernelOp<AlgebraDialect, "vector_fill">;
def VectorGeometricOp : KernelOp<AlgebraDialect, "vector_geometric">;
def FieldFromIndexOp : KernelOp<AlgebraDialect, "field_from_index">;
def CoefficientCountOp : KernelOp<PolynomialDialect, "coefficient_count">;
def CosetEvaluateOp : KernelOp<PolynomialDialect, "coset_evaluate">;
def CosetInterpolateOp : KernelOp<PolynomialDialect, "coset_interpolate">;
def DomainPointOp : KernelOp<PolynomialDialect, "domain_point">;
def DomainRootOp : KernelOp<PolynomialDialect, "domain_root">;
def DomainPointsOp : KernelOp<PolynomialDialect, "domain_points">;
def EvenOddFoldOp : KernelOp<PolynomialDialect, "even_odd_fold">;
def DivideOpeningOp : KernelOp<PolynomialDialect, "divide_opening">;
def OpeningQuotientOp : KernelOp<PolynomialDialect, "opening_quotient">;
def FieldSubtractOp : KernelOp<AlgebraDialect, "subtract">;
def FieldNegateOp : KernelOp<AlgebraDialect, "negate">;
def FieldInverseOp : KernelOp<AlgebraDialect, "inverse">;
def FieldEmbedOp : KernelOp<AlgebraDialect, "embed">;
def MatrixMulVectorOp : KernelOp<AlgebraDialect, "matrix_mul_vector">;
def MatrixTransposeMulVectorOp : KernelOp<AlgebraDialect, "matrix_transpose_mul_vector">;
def MatrixBilinearOp : KernelOp<AlgebraDialect, "matrix_bilinear">;
def MatrixShapeCheckOp : KernelOp<AlgebraDialect, "matrix_shape_check">;
def MatrixIdentityCheckOp : KernelOp<AlgebraDialect, "matrix_identity_check">;
def VectorConstantOp : KernelOp<AlgebraDialect, "vector_constant">;
def VectorScatterSumOp : KernelOp<AlgebraDialect, "vector_scatter_sum">;
def VectorEmptyOp : KernelOp<AlgebraDialect, "vector_empty">;
def VectorAppendOp : KernelOp<AlgebraDialect, "vector_append">;
def VectorSplatOp : KernelOp<AlgebraDialect, "vector_splat">;
def VectorPowersOp : KernelOp<AlgebraDialect, "vector_powers">;
def VectorAddOp : KernelOp<AlgebraDialect, "vector_add">;
def VectorSubOp : KernelOp<AlgebraDialect, "vector_sub">;
def VectorMulOp : KernelOp<AlgebraDialect, "vector_mul", [DeclareOpInterfaceMethods<DiagonalProducerInterface>]>;
def VectorDotOp : KernelOp<AlgebraDialect, "vector_dot", [DeclareOpInterfaceMethods<DiagonalContractionInterface>]>;
def VectorConcatOp : KernelOp<AlgebraDialect, "vector_concat">;
def VectorKroneckerOp : KernelOp<AlgebraDialect, "vector_kronecker">;
def VectorMatvecOp : KernelOp<AlgebraDialect, "vector_matvec">;
def VectorScaleOp : KernelOp<AlgebraDialect, "vector_scale">;
def VectorSumOp : KernelOp<AlgebraDialect, "vector_sum">;
def VectorSplitOp : KernelOp<AlgebraDialect, "vector_split">;
def VectorAtOp : KernelOp<AlgebraDialect, "vector_at">;
def VectorLengthCheckOp : KernelOp<AlgebraDialect, "vector_length_check">;
def VectorGatherOp : KernelOp<AlgebraDialect, "vector_gather">;
def PointToVectorOp : KernelOp<PolynomialDialect, "point_to_vector">;
def TableToVectorOp : KernelOp<PolynomialDialect, "table_to_vector">;
def PointFromVectorOp : KernelOp<PolynomialDialect, "point_from_vector">;
def TableFromVectorOp : KernelOp<PolynomialDialect, "table_from_vector">;
def EqualityWeightsOp : KernelOp<PolynomialDialect, "equality_weights">;
def FromCoefficientsOp : KernelOp<PolynomialDialect, "from_coefficients">;
def CoefficientsOp : KernelOp<PolynomialDialect, "coefficients">;
def DegreeCheckOp : KernelOp<PolynomialDialect, "degree_check">;
def UnivariateEvaluateOp : KernelOp<PolynomialDialect, "univariate_evaluate">;
def UnivariateBoundaryOp : KernelOp<PolynomialDialect, "univariate_boundary">;
def RandomVectorOp : KernelOp<PIRDialect, "random_vector">;
def CurveNegateOp : KernelOp<AlgebraDialect, "curve_negate">;
def CurveNonidentityOp : KernelOp<AlgebraDialect, "curve_nonidentity">;
def CurveMSMOp : KernelOp<AlgebraDialect, "curve_msm", [DeclareOpInterfaceMethods<DiagonalContractionInterface>]>;
def CurveScaleEachOp : KernelOp<AlgebraDialect, "curve_scale_each", [DeclareOpInterfaceMethods<DiagonalProducerInterface>]>;
def CurveVectorAddOp : KernelOp<AlgebraDialect, "curve_vector_add">;
def CurveVectorScaleOp : KernelOp<AlgebraDialect, "curve_vector_scale">;
def CurveSplitOp : KernelOp<AlgebraDialect, "curve_split">;
def CurveConcatOp : KernelOp<AlgebraDialect, "curve_concat">;
// Ordered, equal-length G1/G2 vectors; returns whether the pairing product is
// one. Length mismatch is an operation failure, and the empty product is one.
// Nominal source groups are resolved independently by the binding signature.
def PairingCheckOp : KernelOp<AlgebraDialect, "pairing_check">;

def FieldConstantOp : KernelOp<AlgebraDialect, "constant">;
def FieldSumOp : KernelOp<AlgebraDialect, "sum">;
def FieldProductOp : KernelOp<AlgebraDialect, "product">;
def FieldCompareOp : KernelOp<AlgebraDialect, "compare">;
def BooleanAndOp : KernelOp<PIRDialect, "and">;
def BooleanNotOp : KernelOp<PIRDialect, "not">;
def BooleanOrOp : KernelOp<PIRDialect, "or">;
def RequireOp : KernelOp<PIRDialect, "require">;
def ProductSumOp : KernelOp<PolynomialDialect, "product_sum">;
def ProductRoundOp : KernelOp<PolynomialDialect, "product_round">;
def BoundaryOp : KernelOp<PolynomialDialect, "boundary">;
def RoundEvaluateOp : KernelOp<PolynomialDialect, "round_evaluate">;
def FoldOp : KernelOp<PolynomialDialect, "fold">;
def MLEEvaluateOp : KernelOp<PolynomialDialect, "mle_evaluate">;
def EmptyPointOp : KernelOp<PolynomialDialect, "empty_point">;
def AppendPointOp : KernelOp<PolynomialDialect, "append_point">;
def PCSCommitOp : KernelOp<PCSDialect, "commit">;
def PCSOpenOp : KernelOp<PCSDialect, "open">;
def PCSCheckOp : KernelOp<PCSDialect, "check">;
def RandomIndexOp : KernelOp<PIRDialect, "random_index">;
def TranscriptDrawIndexOp : KernelOp<PIRDialect, "transcript_draw_index">;
def RandomDrawOp : KernelOp<PIRDialect, "random_draw">;

def PCSEqualOp : KernelOp<PCSDialect, "equal">;
def TranscriptObserveOp : KernelOp<PIRDialect, "transcript_observe">;
def TranscriptChallengeOp : KernelOp<PIRDialect, "transcript_challenge">;
def CurveGeneratorOp : KernelOp<AlgebraDialect, "curve_generator">;
def CurveAddOp : KernelOp<AlgebraDialect, "curve_add">;
def CurveScaleOp : KernelOp<AlgebraDialect, "curve_scale">;
def CurveEqualOp : KernelOp<AlgebraDialect, "curve_equal">;
def CurveEmptyOp : KernelOp<AlgebraDialect, "curve_empty">;
def CurveAppendOp : KernelOp<AlgebraDialect, "curve_append">;
def CurveAtOp : KernelOp<AlgebraDialect, "curve_at">;
def CurveGetOp : KernelOp<AlgebraDialect, "curve_get">;
def CurveLengthOp : KernelOp<AlgebraDialect, "curve_length">;
def CurveCommitOp : KernelOp<AlgebraDialect, "curve_commit">;
def CurveResponseOp : KernelOp<AlgebraDialect, "curve_response">;
#endif
