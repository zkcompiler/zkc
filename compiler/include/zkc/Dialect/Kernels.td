#ifndef ZKC_DIALECT_KERNELS_TD
#define ZKC_DIALECT_KERNELS_TD
include "zkc/Dialect/Constraints.td"
include "zkc/Interfaces/LinearContraction.td"
// These mathematical operations retain potential failure: no Pure/speculatable
// marker is inferred merely from a mathematical totality claim. The installed
// verifier checks types, attributes and physical selection. Semantic facets
// live in Contracts/Operations.h; absent facets grant no rewrite permission.
class KernelOp<Dialect dialect, string name, list<string> contracts,
               list<Trait> traits = []>
    : Op<dialect, name, traits>, ZKC_ContractMapping {
  let contractKeys = contracts;
  let arguments = (ins Variadic<Zkc_ProtocolData>:$inputs, StrAttr:$site,
    ArrayAttr:$parameters, OptionalAttr<FlatSymbolRefAttr>:$binding);
  let results = (outs Variadic<Zkc_ProtocolData>:$outputs);
  let hasVerifier = 1;
}
def ResourceUnitCreateOp : KernelOp<PIRDialect, "resource_unit_create", ["resource_unit.create"]> {
  let description = [{
    Creates one zero-payload logical resource unit of the slot named by the
    binding. The unit is affine: it can be passed or consumed once and is
    retired with its frame when neither returned nor consumed (docs/spec/domains/values.md).
  }];
}
def ResourceUnitPassOp : KernelOp<PIRDialect, "resource_unit_pass", ["resource_unit.pass"]> {
  let description = [{
    Moves a resource unit into a fresh occurrence of the same slot. The input
    occurrence is consumed; the operation grants no copy (docs/spec/domains/values.md).
  }];
}
def ResourceUnitConsumeOp : KernelOp<PIRDialect, "resource_unit_consume", ["resource_unit.consume"]> {
  let description = [{
    Consumes a resource unit and produces nothing. It must remain even though
    it has no result, since removing it would change the unit's lifetime and the
    observed operation sequence (docs/spec/domains/values.md).
  }];
}
def OracleCommitOp : KernelOp<OracleDialect, "commit", ["oracle.commit"]>;
def OracleOpenOp : KernelOp<OracleDialect, "open", ["oracle.open"]>;
def OracleCheckOp : KernelOp<OracleDialect, "check", ["oracle.check"]>;
def CommitmentsEmptyOp : KernelOp<OracleDialect, "commitments_empty", ["commitments.empty"]>;
def CommitmentsAppendOp : KernelOp<OracleDialect, "commitments_append", ["commitments.append"]>;
def CommitmentsAtOp : KernelOp<OracleDialect, "commitments_at", ["commitments.at"]>;
def CommitmentsLengthOp : KernelOp<OracleDialect, "commitments_length", ["commitments.length"]>;
def OpeningStatesEmptyOp : KernelOp<OracleDialect, "opening_states_empty", ["opening_states.empty"]>;
def OpeningStatesAppendOp : KernelOp<OracleDialect, "opening_states_append", ["opening_states.append"]>;
def OpeningStatesAtOp : KernelOp<OracleDialect, "opening_states_at", ["opening_states.at"]>;
def OpeningStatesLengthOp : KernelOp<OracleDialect, "opening_states_length", ["opening_states.length"]>;
def ExternalMoneroInitOp : KernelOp<AlgebraDialect, "external_monero_init", ["external.monero.init"]> {
  let description = [{
    Starts the pinned Monero scalar hash chain from its initial bytes.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalMoneroHashOp : KernelOp<AlgebraDialect, "external_monero_hash", ["external.monero.hash"]> {
  let description = [{
    Hashes concatenated words to Monero scalar bytes without a chain state.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalMoneroUpdateOp : KernelOp<AlgebraDialect, "external_monero_update", ["external.monero.update"]> {
  let description = [{
    Absorbs concatenated words into the Monero hash chain; returns the successor state and the derived scalar bytes.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalOpenvmInitOp : KernelOp<AlgebraDialect, "external_openvm_init", ["external.openvm.init"]> {
  let description = [{
    Starts the pinned OpenVM BabyBear Poseidon2 duplex state.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalOpenvmObserveOp : KernelOp<AlgebraDialect, "external_openvm_observe", ["external.openvm.observe"]> {
  let description = [{
    Absorbs field words into the OpenVM duplex; returns the successor state.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalOpenvmSampleOp : KernelOp<AlgebraDialect, "external_openvm_sample", ["external.openvm.sample"]> {
  let description = [{
    Squeezes one base-field sample from the OpenVM duplex.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalOpenvmSampleExtOp : KernelOp<AlgebraDialect, "external_openvm_sample_ext", ["external.openvm.sample_ext"]> {
  let description = [{
    Squeezes the four coefficients of one quartic-extension sample.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalOpenvmSampleBitsOp : KernelOp<AlgebraDialect, "external_openvm_sample_bits", ["external.openvm.sample_bits"]> {
  let description = [{
    Squeezes a sample and masks it to the requested number of bits, as the pinned query sampler does.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def ExternalOpenvmCheckWitnessOp : KernelOp<AlgebraDialect, "external_openvm_check_witness", ["external.openvm.check_witness"]> {
  let description = [{
    Checks a grinding witness against the requested number of bits on the live state.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}
def IndexConstantOp : KernelOp<AlgebraDialect, "index_constant", ["index.constant"]>;
def IndexAddOp : KernelOp<AlgebraDialect, "index_add", ["index.add"]>;
def IndexSubOp : KernelOp<AlgebraDialect, "index_sub", ["index.sub"]>;
def IndexMulOp : KernelOp<AlgebraDialect, "index_mul", ["index.mul"]>;
def IndexDivOp : KernelOp<AlgebraDialect, "index_div", ["index.div"]>;
def IndexModOp : KernelOp<AlgebraDialect, "index_mod", ["index.mod"]>;
def IndexEqualOp : KernelOp<AlgebraDialect, "index_equal", ["index.equal"]>;
def IndexLessOp : KernelOp<AlgebraDialect, "index_less", ["index.less"]>;
def IndicesEmptyOp : KernelOp<AlgebraDialect, "indices_empty", ["indices.empty"]>;
def IndicesAppendOp : KernelOp<AlgebraDialect, "indices_append", ["indices.append"]>;
def IndicesAtOp : KernelOp<AlgebraDialect, "indices_at", ["indices.at"]>;
def IndicesLengthOp : KernelOp<AlgebraDialect, "indices_length", ["indices.length"]>;
def VectorGetOp : KernelOp<AlgebraDialect, "vector_get", ["vector.get"]>;
def VectorSliceOp : KernelOp<AlgebraDialect, "vector_slice", ["vector.slice"]>;
def VectorLengthOp : KernelOp<AlgebraDialect, "vector_length", ["vector.length"]>;
def VectorRotateOp : KernelOp<AlgebraDialect, "vector_rotate", ["vector.rotate"]>;
def VectorInterleaveOp : KernelOp<AlgebraDialect, "vector_interleave", ["vector.interleave"]>;
def VectorPrefixProductOp : KernelOp<AlgebraDialect, "vector_prefix_product", ["vector.prefix_product"]>;
def VectorPrefixSumOp : KernelOp<AlgebraDialect, "vector_prefix_sum", ["vector.prefix_sum"]>;
def VectorInverseOp : KernelOp<AlgebraDialect, "vector_inverse", ["vector.inverse"]>;
def VectorEmbedOp : KernelOp<AlgebraDialect, "vector_embed", ["vector.embed"]>;
def VectorFillOp : KernelOp<AlgebraDialect, "vector_fill", ["vector.fill"]>;
def VectorGeometricOp : KernelOp<AlgebraDialect, "vector_geometric", ["vector.geometric"]>;
def FieldFromIndexOp : KernelOp<AlgebraDialect, "field_from_index", ["field.from_index"]>;
def CoefficientCountOp : KernelOp<PolynomialDialect, "coefficient_count", ["poly.coefficient_count"]>;
def CosetEvaluateOp : KernelOp<PolynomialDialect, "coset_evaluate", ["poly.coset_evaluate"]>;
def CosetInterpolateOp : KernelOp<PolynomialDialect, "coset_interpolate", ["poly.coset_interpolate"]>;
def DomainPointOp : KernelOp<PolynomialDialect, "domain_point", ["poly.domain_point"]>;
def DomainRootOp : KernelOp<PolynomialDialect, "domain_root", ["poly.domain_root"]>;
def DomainPointsOp : KernelOp<PolynomialDialect, "domain_points", ["poly.domain_points"]>;
def EvenOddFoldOp : KernelOp<PolynomialDialect, "even_odd_fold", ["poly.even_odd_fold"]>;
def DivideOpeningOp : KernelOp<PolynomialDialect, "divide_opening", ["poly.divide_opening"]>;
def OpeningQuotientOp : KernelOp<PolynomialDialect, "opening_quotient", ["poly.opening_quotient"]>;
def FieldSubtractOp : KernelOp<AlgebraDialect, "subtract", ["field.sub"]>;
def FieldNegateOp : KernelOp<AlgebraDialect, "negate", ["field.neg"]>;
def FieldInverseOp : KernelOp<AlgebraDialect, "inverse", ["field.inverse"]>;
def FieldEmbedOp : KernelOp<AlgebraDialect, "embed", ["field.embed"]>;
def MatrixMulVectorOp : KernelOp<AlgebraDialect, "matrix_mul_vector", ["matrix.mul_vector"]>;
def MatrixTransposeMulVectorOp : KernelOp<AlgebraDialect, "matrix_transpose_mul_vector", ["matrix.transpose_mul_vector"]>;
def MatrixBilinearOp : KernelOp<AlgebraDialect, "matrix_bilinear", ["matrix.bilinear"]>;
def MatrixShapeCheckOp : KernelOp<AlgebraDialect, "matrix_shape_check", ["matrix.shape_check"]>;
def MatrixIdentityCheckOp : KernelOp<AlgebraDialect, "matrix_identity_check", ["matrix.identity_check"]>;
def VectorConstantOp : KernelOp<AlgebraDialect, "vector_constant", ["vector.constant"]>;
def VectorScatterSumOp : KernelOp<AlgebraDialect, "vector_scatter_sum", ["vector.scatter_sum"]>;
def VectorEmptyOp : KernelOp<AlgebraDialect, "vector_empty", ["vector.empty"]>;
def VectorAppendOp : KernelOp<AlgebraDialect, "vector_append", ["vector.append"]>;
def VectorSplatOp : KernelOp<AlgebraDialect, "vector_splat", ["vector.splat"]>;
def VectorPowersOp : KernelOp<AlgebraDialect, "vector_powers", ["vector.powers"]>;
def VectorAddOp : KernelOp<AlgebraDialect, "vector_add", ["vector.add"]>;
def VectorSubOp : KernelOp<AlgebraDialect, "vector_sub", ["vector.sub"]>;
def VectorMulOp : KernelOp<AlgebraDialect, "vector_mul", ["vector.mul"], [DeclareOpInterfaceMethods<DiagonalProducerInterface>]>;
def VectorDotOp : KernelOp<AlgebraDialect, "vector_dot", ["vector.dot"], [DeclareOpInterfaceMethods<DiagonalContractionInterface>]>;
def VectorConcatOp : KernelOp<AlgebraDialect, "vector_concat", ["vector.concat"]>;
def VectorKroneckerOp : KernelOp<AlgebraDialect, "vector_kronecker", ["vector.kronecker"]>;
def VectorMatvecOp : KernelOp<AlgebraDialect, "vector_matvec", ["vector.matvec"]>;
def VectorScaleOp : KernelOp<AlgebraDialect, "vector_scale", ["vector.scale"]>;
def VectorSumOp : KernelOp<AlgebraDialect, "vector_sum", ["vector.sum"]>;
def VectorSplitOp : KernelOp<AlgebraDialect, "vector_split", ["vector.split"]>;
def VectorAtOp : KernelOp<AlgebraDialect, "vector_at", ["vector.at"]>;
def VectorLengthCheckOp : KernelOp<AlgebraDialect, "vector_length_check", ["vector.length_check"]>;
def VectorGatherOp : KernelOp<AlgebraDialect, "vector_gather", ["vector.gather"]>;
def PointToVectorOp : KernelOp<PolynomialDialect, "point_to_vector", ["vector.from_point"]>;
def TableToVectorOp : KernelOp<PolynomialDialect, "table_to_vector", ["vector.from_table"]>;
def PointFromVectorOp : KernelOp<PolynomialDialect, "point_from_vector", ["vector.to_point"]>;
def TableFromVectorOp : KernelOp<PolynomialDialect, "table_from_vector", ["vector.to_table"]>;
def EqualityWeightsOp : KernelOp<PolynomialDialect, "equality_weights", ["poly.equality_weights"]>;
def FromCoefficientsOp : KernelOp<PolynomialDialect, "from_coefficients", ["poly.from_coefficients"]>;
def CoefficientsOp : KernelOp<PolynomialDialect, "coefficients", ["poly.coefficients"]>;
def DegreeCheckOp : KernelOp<PolynomialDialect, "degree_check", ["poly.degree_check"]>;
def UnivariateEvaluateOp : KernelOp<PolynomialDialect, "univariate_evaluate", ["poly.univariate_evaluate"]>;
def UnivariateBoundaryOp : KernelOp<PolynomialDialect, "univariate_boundary", ["poly.univariate_boundary"]>;
def RandomVectorOp : KernelOp<PIRDialect, "random_vector", ["random.vector"]>;
def CurveNegateOp : KernelOp<AlgebraDialect, "curve_negate", ["curve.neg"]>;
def CurveNonidentityOp : KernelOp<AlgebraDialect, "curve_nonidentity", ["curve.nonidentity"]>;
def CurveMSMOp : KernelOp<AlgebraDialect, "curve_msm", ["curve.msm"], [DeclareOpInterfaceMethods<DiagonalContractionInterface>]>;
def CurveScaleEachOp : KernelOp<AlgebraDialect, "curve_scale_each", ["curve.scale_each"], [DeclareOpInterfaceMethods<DiagonalProducerInterface>]>;
def CurveVectorAddOp : KernelOp<AlgebraDialect, "curve_vector_add", ["curve.vector_add"]>;
def CurveVectorScaleOp : KernelOp<AlgebraDialect, "curve_vector_scale", ["curve.vector_scale"]>;
def CurveSplitOp : KernelOp<AlgebraDialect, "curve_split", ["curve.split"]>;
def CurveConcatOp : KernelOp<AlgebraDialect, "curve_concat", ["curve.concat"]>;
// Ordered, equal-length G1/G2 vectors; returns whether the pairing product is
// one. Length mismatch is an operation failure, and the empty product is one.
// Nominal source groups are resolved independently by the binding signature.
def PairingCheckOp : KernelOp<AlgebraDialect, "pairing_check", ["pairing.check"]>;

def FieldConstantOp : KernelOp<AlgebraDialect, "constant", ["field.constant"]>;
def FieldSumOp : KernelOp<AlgebraDialect, "sum", ["field.add"]>;
def FieldProductOp : KernelOp<AlgebraDialect, "product", ["field.mul"]>;
def FieldCompareOp : KernelOp<AlgebraDialect, "compare", ["field.equal"]>;
def BooleanAndOp : KernelOp<PIRDialect, "and", ["bool.and"]>;
def BooleanNotOp : KernelOp<PIRDialect, "not", ["bool.not"]>;
def BooleanOrOp : KernelOp<PIRDialect, "or", ["bool.or"]>;
def RequireOp : KernelOp<PIRDialect, "require", ["control.require"]>;
def ProductSumOp : KernelOp<PolynomialDialect, "product_sum", ["poly.product_sum"]>;
def ProductRoundOp : KernelOp<PolynomialDialect, "product_round", ["poly.product_round"]>;
def BoundaryOp : KernelOp<PolynomialDialect, "boundary", ["poly.boundary"]>;
def RoundEvaluateOp : KernelOp<PolynomialDialect, "round_evaluate", ["poly.round_evaluate"]>;
def FoldOp : KernelOp<PolynomialDialect, "fold", ["poly.fold"]>;
def MLEEvaluateOp : KernelOp<PolynomialDialect, "mle_evaluate", ["poly.evaluate"]>;
def EmptyPointOp : KernelOp<PolynomialDialect, "empty_point", ["poly.empty_point"]>;
def AppendPointOp : KernelOp<PolynomialDialect, "append_point", ["poly.append_point"]>;
def PCSCommitOp : KernelOp<PCSDialect, "commit", ["pcs.commit"]>;
def PCSOpenOp : KernelOp<PCSDialect, "open", ["pcs.open"]>;
def PCSCheckOp : KernelOp<PCSDialect, "check", ["pcs.check"]>;
def RandomIndexOp : KernelOp<PIRDialect, "random_index", ["random.index"]>;
def TranscriptDrawIndexOp : KernelOp<PIRDialect, "transcript_draw_index", ["transcript.draw_index"]>;
def RandomDrawOp : KernelOp<PIRDialect, "random_draw", ["random.draw"]>;

def PCSEqualOp : KernelOp<PCSDialect, "equal", ["pcs.equal"]>;
def TranscriptObserveOp : KernelOp<PIRDialect, "transcript_observe", []> {
  // Only installed contracts in this family acquire an IR association.
  let contractFamilies = ["transcript.observe."];
}
def TranscriptChallengeOp : KernelOp<PIRDialect, "transcript_challenge", ["transcript.challenge"]>;
def CurveGeneratorOp : KernelOp<AlgebraDialect, "curve_generator", ["curve.generator"]>;
def CurveAddOp : KernelOp<AlgebraDialect, "curve_add", ["curve.add"]>;
def CurveScaleOp : KernelOp<AlgebraDialect, "curve_scale", ["curve.scale"]>;
def CurveEqualOp : KernelOp<AlgebraDialect, "curve_equal", ["curve.equal"]>;
def CurveEmptyOp : KernelOp<AlgebraDialect, "curve_empty", ["curve.empty"]>;
def CurveAppendOp : KernelOp<AlgebraDialect, "curve_append", ["curve.append"]>;
def CurveAtOp : KernelOp<AlgebraDialect, "curve_at", ["curve.at"]>;
def CurveGetOp : KernelOp<AlgebraDialect, "curve_get", ["curve.get"]>;
def CurveLengthOp : KernelOp<AlgebraDialect, "curve_length", ["curve.length"]>;
def CurveCommitOp : KernelOp<AlgebraDialect, "curve_commit", ["curve.commit"]>;
def CurveResponseOp : KernelOp<AlgebraDialect, "curve_response", ["curve.response"]>;
#endif
