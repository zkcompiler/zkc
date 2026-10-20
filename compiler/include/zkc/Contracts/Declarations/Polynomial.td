// Logical contracts and curated exports owned by this domain.
def OpPolyCoefficientCountF : ZKC_Root<"F", FieldDomain>;
def OpPolyCoefficientCount : ZKC_Operation<"poly.coefficient_count", [OpPolyCoefficientCountF],
    [ZKC_Apply<TypePolynomial, [OpPolyCoefficientCountF]>],
    [ZKC_Apply<TypeIndex, []>], [ZKC_Holds<CapabilityCommRing, [OpPolyCoefficientCountF]>]> {
  int ordinal = 36;
}

def OpPolyCosetEvaluateF : ZKC_Root<"F", FieldDomain>;
def OpPolyCosetEvaluate : ZKC_Operation<"poly.coset_evaluate", [OpPolyCosetEvaluateF],
    [ZKC_Apply<TypePolynomial, [OpPolyCosetEvaluateF]>, ZKC_Apply<TypeField, [OpPolyCosetEvaluateF]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeVector, [OpPolyCosetEvaluateF]>], [ZKC_Holds<CapabilityTwoAdicField, [OpPolyCosetEvaluateF]>]> {
  int ordinal = 37;
  let facets = [ZKC_Coset<1, 2, 0, 0, 0>];
}

def OpPolyCosetInterpolateF : ZKC_Root<"F", FieldDomain>;
def OpPolyCosetInterpolate : ZKC_Operation<"poly.coset_interpolate", [OpPolyCosetInterpolateF],
    [ZKC_Apply<TypeVector, [OpPolyCosetInterpolateF]>, ZKC_Apply<TypeField, [OpPolyCosetInterpolateF]>],
    [ZKC_Apply<TypePolynomial, [OpPolyCosetInterpolateF]>], [ZKC_Holds<CapabilityTwoAdicField, [OpPolyCosetInterpolateF]>]> {
  int ordinal = 38;
  let facets = [ZKC_Coset<1, 0, 1, -1, 0>];
}

// Coefficient blocks share one ordered output coset. Representation padding
// belongs to the caller; a flattened batch has no single-word Coset facet.
def OpPolyCosetEvaluateBatchF : ZKC_Root<"F", FieldDomain>;
def OpPolyCosetEvaluateBatch : ZKC_Operation<"poly.coset_evaluate_batch", [OpPolyCosetEvaluateBatchF],
    [ZKC_Apply<TypeVector, [OpPolyCosetEvaluateBatchF]>,
     ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>,
     ZKC_Apply<TypeField, [OpPolyCosetEvaluateBatchF]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeVector, [OpPolyCosetEvaluateBatchF]>],
    [ZKC_Holds<CapabilityTwoAdicField, [OpPolyCosetEvaluateBatchF]>]>;

// Each column has its own interpolant, in canonical column-major order.
// A flattened batch is not one evaluation word: the single-word Coset facet
// must not associate its total length with either column domain.
def OpPolyCosetExtendF : ZKC_Root<"F", FieldDomain>;
def OpPolyCosetExtend : ZKC_Operation<"poly.coset_extend", [OpPolyCosetExtendF],
    [ZKC_Apply<TypeVector, [OpPolyCosetExtendF]>,
     ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>,
     ZKC_Apply<TypeField, [OpPolyCosetExtendF]>,
     ZKC_Apply<TypeField, [OpPolyCosetExtendF]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeVector, [OpPolyCosetExtendF]>],
    [ZKC_Holds<CapabilityTwoAdicField, [OpPolyCosetExtendF]>]>;

// Point evaluation shares one ordered domain across independent columns.
// A flattened batch does not carry a single-word Coset facet.
def OpPolyCosetEvaluateAtF : ZKC_Root<"F", FieldDomain>;
def OpPolyCosetEvaluateAt : ZKC_Operation<"poly.coset_evaluate_at", [OpPolyCosetEvaluateAtF],
    [ZKC_Apply<TypeVector, [OpPolyCosetEvaluateAtF]>,
     ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>,
     ZKC_Apply<TypeField, [OpPolyCosetEvaluateAtF]>,
     ZKC_Apply<TypeField, [OpPolyCosetEvaluateAtF]>],
    [ZKC_Apply<TypeVector, [OpPolyCosetEvaluateAtF]>],
    [ZKC_Holds<CapabilityTwoAdicField, [OpPolyCosetEvaluateAtF]>]>;

def OpPolyDomainPointF : ZKC_Root<"F", FieldDomain>;
def OpPolyDomainPoint : ZKC_Operation<"poly.domain_point", [OpPolyDomainPointF],
    [ZKC_Apply<TypeField, [OpPolyDomainPointF]>, ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeField, [OpPolyDomainPointF]>], [ZKC_Holds<CapabilityTwoAdicField, [OpPolyDomainPointF]>]> {
  int ordinal = 39;
  let facets = [ZKC_Coset<0, 1, 0, -1, 0>];
}

def OpPolyDomainRootF : ZKC_Root<"F", FieldDomain>;
def OpPolyDomainRoot : ZKC_Operation<"poly.domain_root", [OpPolyDomainRootF],
    [ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeField, [OpPolyDomainRootF]>], [ZKC_Holds<CapabilityTwoAdicField, [OpPolyDomainRootF]>]> {
  int ordinal = 40;
}

def OpPolyDomainPointsF : ZKC_Root<"F", FieldDomain>;
def OpPolyDomainPoints : ZKC_Operation<"poly.domain_points", [OpPolyDomainPointsF],
    [ZKC_Apply<TypeField, [OpPolyDomainPointsF]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeVector, [OpPolyDomainPointsF]>], [ZKC_Holds<CapabilityTwoAdicField, [OpPolyDomainPointsF]>]> {
  int ordinal = 41;
  let facets = [ZKC_Coset<0, 1, 0, 0, 0>];
}

def OpPolyEvenOddFoldF : ZKC_Root<"F", FieldDomain>;
def OpPolyEvenOddFold : ZKC_Operation<"poly.even_odd_fold", [OpPolyEvenOddFoldF],
    [ZKC_Apply<TypeVector, [OpPolyEvenOddFoldF]>, ZKC_Apply<TypeField, [OpPolyEvenOddFoldF]>, ZKC_Apply<TypeField, [OpPolyEvenOddFoldF]>],
    [ZKC_Apply<TypeVector, [OpPolyEvenOddFoldF]>], [ZKC_Holds<CapabilityTwoAdicField, [OpPolyEvenOddFoldF]>, ZKC_Holds<CapabilityCharacteristicNotTwo, [OpPolyEvenOddFoldF]>]> {
  int ordinal = 42;
  let facets = [ZKC_Coset<1, 0, 1, 0, 1>];
}

def OpPolyDivideOpeningF : ZKC_Root<"F", FieldDomain>;
def OpPolyDivideOpening : ZKC_Operation<"poly.divide_opening", [OpPolyDivideOpeningF],
    [ZKC_Apply<TypePolynomial, [OpPolyDivideOpeningF]>, ZKC_Apply<TypeField, [OpPolyDivideOpeningF]>, ZKC_Apply<TypeField, [OpPolyDivideOpeningF]>],
    [ZKC_Apply<TypePolynomial, [OpPolyDivideOpeningF]>], [ZKC_Holds<CapabilityCommRing, [OpPolyDivideOpeningF]>]> {
  int ordinal = 43;
}

def OpPolyOpeningQuotientF : ZKC_Root<"F", FieldDomain>;
def OpPolyOpeningQuotient : ZKC_Operation<"poly.opening_quotient", [OpPolyOpeningQuotientF],
    [ZKC_Apply<TypeVector, [OpPolyOpeningQuotientF]>, ZKC_Apply<TypeField, [OpPolyOpeningQuotientF]>, ZKC_Apply<TypeField, [OpPolyOpeningQuotientF]>, ZKC_Apply<TypeField, [OpPolyOpeningQuotientF]>],
    [ZKC_Apply<TypeVector, [OpPolyOpeningQuotientF]>], [ZKC_Holds<CapabilityTwoAdicField, [OpPolyOpeningQuotientF]>]> {
  int ordinal = 44;
  let facets = [ZKC_Coset<1, 0, 1, 0, 0>];
}

// A weighted rational combination of selected column-major words. Its result
// has one domain's height, not the flattened input's length. No opening,
// authentication or degree claim follows from this arithmetic operation.
def OpPolyOpeningQuotientSumF : ZKC_Root<"F", FieldDomain>;
def OpPolyOpeningQuotientSum : ZKC_Operation<"poly.opening_quotient_sum", [OpPolyOpeningQuotientSumF],
    [ZKC_Apply<TypeVector, [OpPolyOpeningQuotientSumF]>,
     ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>,
     ZKC_Apply<TypeField, [OpPolyOpeningQuotientSumF]>,
     ZKC_Apply<TypeIndices, []>,
     ZKC_Apply<TypeVector, [OpPolyOpeningQuotientSumF]>,
     ZKC_Apply<TypeVector, [OpPolyOpeningQuotientSumF]>,
     ZKC_Apply<TypeVector, [OpPolyOpeningQuotientSumF]>,
     ZKC_Apply<TypeVector, [OpPolyOpeningQuotientSumF]>],
    [ZKC_Apply<TypeVector, [OpPolyOpeningQuotientSumF]>],
    [ZKC_Holds<CapabilityTwoAdicField, [OpPolyOpeningQuotientSumF]>]>;

def OpPolyEqualityWeightsF : ZKC_Root<"F", FieldDomain>;
def OpPolyEqualityWeights : ZKC_Operation<"poly.equality_weights", [OpPolyEqualityWeightsF],
    [ZKC_Apply<TypePoint, [OpPolyEqualityWeightsF]>],
    [ZKC_Apply<TypeVector, [OpPolyEqualityWeightsF]>], [ZKC_Holds<CapabilityCommRing, [OpPolyEqualityWeightsF]>]> {
  int ordinal = 77;
}

def OpPolyFromCoefficientsF : ZKC_Root<"F", FieldDomain>;
def OpPolyFromCoefficients : ZKC_Operation<"poly.from_coefficients", [OpPolyFromCoefficientsF],
    [ZKC_Apply<TypeVector, [OpPolyFromCoefficientsF]>],
    [ZKC_Apply<TypePolynomial, [OpPolyFromCoefficientsF]>], [ZKC_Holds<CapabilityCommRing, [OpPolyFromCoefficientsF]>]> {
  int ordinal = 78;
}

def OpPolyCoefficientsF : ZKC_Root<"F", FieldDomain>;
def OpPolyCoefficients : ZKC_Operation<"poly.coefficients", [OpPolyCoefficientsF],
    [ZKC_Apply<TypePolynomial, [OpPolyCoefficientsF]>],
    [ZKC_Apply<TypeVector, [OpPolyCoefficientsF]>], [ZKC_Holds<CapabilityCommRing, [OpPolyCoefficientsF]>]> {
  int ordinal = 79;
}

def OpPolyDegreeCheckF : ZKC_Root<"F", FieldDomain>;
def OpPolyDegreeCheck : ZKC_Operation<"poly.degree_check", [OpPolyDegreeCheckF],
    [ZKC_Apply<TypePolynomial, [OpPolyDegreeCheckF]>],
    [ZKC_Apply<TypeBool, []>], [ZKC_Holds<CapabilityCommRing, [OpPolyDegreeCheckF]>]> {
  int ordinal = 80;
  let parameters = ExtentParameter;
}

def OpPolyUnivariateEvaluateF : ZKC_Root<"F", FieldDomain>;
def OpPolyUnivariateEvaluate : ZKC_Operation<"poly.univariate_evaluate", [OpPolyUnivariateEvaluateF],
    [ZKC_Apply<TypePolynomial, [OpPolyUnivariateEvaluateF]>, ZKC_Apply<TypeField, [OpPolyUnivariateEvaluateF]>],
    [ZKC_Apply<TypeField, [OpPolyUnivariateEvaluateF]>], [ZKC_Holds<CapabilityCommRing, [OpPolyUnivariateEvaluateF]>]> {
  int ordinal = 81;
}

def OpPolyUnivariateBoundaryF : ZKC_Root<"F", FieldDomain>;
def OpPolyUnivariateBoundary : ZKC_Operation<"poly.univariate_boundary", [OpPolyUnivariateBoundaryF],
    [ZKC_Apply<TypePolynomial, [OpPolyUnivariateBoundaryF]>],
    [ZKC_Apply<TypeField, [OpPolyUnivariateBoundaryF]>], [ZKC_Holds<CapabilityCommRing, [OpPolyUnivariateBoundaryF]>]> {
  int ordinal = 82;
}

def OpPolyProductSumF : ZKC_Root<"F", FieldDomain>;
def OpPolyProductSum : ZKC_Operation<"poly.product_sum", [OpPolyProductSumF],
    [ZKC_Apply<TypeTable, [OpPolyProductSumF]>, ZKC_Apply<TypeTable, [OpPolyProductSumF]>],
    [ZKC_Apply<TypeField, [OpPolyProductSumF]>], [ZKC_Holds<CapabilityCommRing, [OpPolyProductSumF]>]> {
  int ordinal = 101;
}

def OpPolyProductRoundF : ZKC_Root<"F", FieldDomain>;
def OpPolyProductRound : ZKC_Operation<"poly.product_round", [OpPolyProductRoundF],
    [ZKC_Apply<TypeTable, [OpPolyProductRoundF]>, ZKC_Apply<TypeTable, [OpPolyProductRoundF]>],
    [ZKC_Apply<TypeRound, [OpPolyProductRoundF]>], [ZKC_Holds<CapabilityCommRing, [OpPolyProductRoundF]>]> {
  int ordinal = 102;
}

def OpPolyBoundaryF : ZKC_Root<"F", FieldDomain>;
def OpPolyBoundary : ZKC_Operation<"poly.boundary", [OpPolyBoundaryF],
    [ZKC_Apply<TypeRound, [OpPolyBoundaryF]>],
    [ZKC_Apply<TypeField, [OpPolyBoundaryF]>], [ZKC_Holds<CapabilityCommRing, [OpPolyBoundaryF]>]> {
  int ordinal = 103;
  let facets = [PublicReplay];
}

def OpPolyRoundEvaluateF : ZKC_Root<"F", FieldDomain>;
def OpPolyRoundEvaluate : ZKC_Operation<"poly.round_evaluate", [OpPolyRoundEvaluateF],
    [ZKC_Apply<TypeRound, [OpPolyRoundEvaluateF]>, ZKC_Apply<TypeField, [OpPolyRoundEvaluateF]>],
    [ZKC_Apply<TypeField, [OpPolyRoundEvaluateF]>], [ZKC_Holds<CapabilityCommRing, [OpPolyRoundEvaluateF]>]> {
  int ordinal = 104;
  let facets = [PublicReplay];
}

def OpPolyFoldF : ZKC_Root<"F", FieldDomain>;
def OpPolyFold : ZKC_Operation<"poly.fold", [OpPolyFoldF],
    [ZKC_Apply<TypeTable, [OpPolyFoldF]>, ZKC_Apply<TypeField, [OpPolyFoldF]>],
    [ZKC_Apply<TypeTable, [OpPolyFoldF]>], [ZKC_Holds<CapabilityCommRing, [OpPolyFoldF]>]> {
  int ordinal = 105;
}

def OpPolyEvaluateF : ZKC_Root<"F", FieldDomain>;
def OpPolyEvaluate : ZKC_Operation<"poly.evaluate", [OpPolyEvaluateF],
    [ZKC_Apply<TypeTable, [OpPolyEvaluateF]>, ZKC_Apply<TypePoint, [OpPolyEvaluateF]>],
    [ZKC_Apply<TypeField, [OpPolyEvaluateF]>], [ZKC_Holds<CapabilityCommRing, [OpPolyEvaluateF]>]> {
  int ordinal = 106;
}

def OpPolyEmptyPointF : ZKC_Root<"F", FieldDomain>;
def OpPolyEmptyPoint : ZKC_Operation<"poly.empty_point", [OpPolyEmptyPointF],
    [],
    [ZKC_Apply<TypePoint, [OpPolyEmptyPointF]>], [ZKC_Holds<CapabilityCommRing, [OpPolyEmptyPointF]>]> {
  int ordinal = 107;
  let facets = [PublicReplay];
}

def OpPolyAppendPointF : ZKC_Root<"F", FieldDomain>;
def OpPolyAppendPoint : ZKC_Operation<"poly.append_point", [OpPolyAppendPointF],
    [ZKC_Apply<TypePoint, [OpPolyAppendPointF]>, ZKC_Apply<TypeField, [OpPolyAppendPointF]>],
    [ZKC_Apply<TypePoint, [OpPolyAppendPointF]>], [ZKC_Holds<CapabilityCommRing, [OpPolyAppendPointF]>]> {
  int ordinal = 108;
  let facets = [PublicReplay];
}

// Current ordered arity of a dynamically shaped multilinear table.
def OpPolyTableArityF : ZKC_Root<"F", FieldDomain>;
def OpPolyTableArity : ZKC_Operation<"poly.table_arity", [OpPolyTableArityF],
    [ZKC_Apply<TypeTable, [OpPolyTableArityF]>], [ZKC_Apply<TypeIndex, []>],
    [ZKC_Holds<CapabilityCommRing, [OpPolyTableArityF]>]>;
