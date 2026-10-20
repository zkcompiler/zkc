#ifndef ZKC_DIALECT_POLYNOMIAL_IR_POLYNOMIALOPS_TD
#define ZKC_DIALECT_POLYNOMIAL_IR_POLYNOMIALOPS_TD

include "zkc/Dialect/Types.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "zkc/Dialect/BoundOperations.td"

def AppendPointOp : BoundOp<PolynomialDialect, "exec.append_point", [OpPolyAppendPoint]>;

def BoundaryOp : BoundOp<PolynomialDialect, "exec.boundary", [OpPolyBoundary]>;

def CoefficientCountOp : BoundOp<PolynomialDialect, "exec.coefficient_count", [OpPolyCoefficientCount]>;

def CoefficientsOp : BoundOp<PolynomialDialect, "exec.coefficients", [OpPolyCoefficients]>;

def CosetEvaluateOp : BoundOp<PolynomialDialect, "exec.coset_evaluate", [OpPolyCosetEvaluate]>;

def CosetEvaluateBatchOp : BoundOp<PolynomialDialect, "exec.coset_evaluate_batch", [OpPolyCosetEvaluateBatch]>;

def CosetEvaluateAtOp : BoundOp<PolynomialDialect, "exec.coset_evaluate_at", [OpPolyCosetEvaluateAt]>;

def CosetExtendOp : BoundOp<PolynomialDialect, "exec.coset_extend", [OpPolyCosetExtend]>;

def CosetInterpolateOp : BoundOp<PolynomialDialect, "exec.coset_interpolate", [OpPolyCosetInterpolate]>;

def DegreeCheckOp : BoundOp<PolynomialDialect, "exec.degree_check", [OpPolyDegreeCheck]>;

def DivideOpeningOp : BoundOp<PolynomialDialect, "exec.divide_opening", [OpPolyDivideOpening]>;

def DomainPointOp : BoundOp<PolynomialDialect, "exec.domain_point", [OpPolyDomainPoint]>;

def DomainPointsOp : BoundOp<PolynomialDialect, "exec.domain_points", [OpPolyDomainPoints]>;

def DomainRootOp : BoundOp<PolynomialDialect, "exec.domain_root", [OpPolyDomainRoot]>;

def EmptyPointOp : BoundOp<PolynomialDialect, "exec.empty_point", [OpPolyEmptyPoint]>;

def EqualityWeightsOp : BoundOp<PolynomialDialect, "exec.equality_weights", [OpPolyEqualityWeights]>;

def EvenOddFoldOp : BoundOp<PolynomialDialect, "exec.even_odd_fold", [OpPolyEvenOddFold]>;

def FoldOp : BoundOp<PolynomialDialect, "exec.fold", [OpPolyFold]>;

def FromCoefficientsOp : BoundOp<PolynomialDialect, "exec.from_coefficients", [OpPolyFromCoefficients]>;

def MLEEvaluateOp : BoundOp<PolynomialDialect, "exec.mle_evaluate", [OpPolyEvaluate]>;

def OpeningQuotientOp : BoundOp<PolynomialDialect, "exec.opening_quotient", [OpPolyOpeningQuotient]>;

def OpeningQuotientSumOp : BoundOp<PolynomialDialect, "exec.opening_quotient_sum", [OpPolyOpeningQuotientSum]>;

def PointFromVectorOp : BoundOp<PolynomialDialect, "exec.point_from_vector", [OpVectorToPoint]>;

def PointToVectorOp : BoundOp<PolynomialDialect, "exec.point_to_vector", [OpVectorFromPoint]>;

def ProductRoundOp : BoundOp<PolynomialDialect, "exec.product_round", [OpPolyProductRound]>;

def ProductSumOp : BoundOp<PolynomialDialect, "exec.product_sum", [OpPolyProductSum]>;

def RoundEvaluateOp : BoundOp<PolynomialDialect, "exec.round_evaluate", [OpPolyRoundEvaluate]>;

def TableArityOp : BoundOp<PolynomialDialect, "exec.table_arity", [OpPolyTableArity]>;

def TableFromVectorOp : BoundOp<PolynomialDialect, "exec.table_from_vector", [OpVectorToTable]>;

def TableToVectorOp : BoundOp<PolynomialDialect, "exec.table_to_vector", [OpVectorFromTable]>;

def UnivariateBoundaryOp : BoundOp<PolynomialDialect, "exec.univariate_boundary", [OpPolyUnivariateBoundary]>;

def UnivariateEvaluateOp : BoundOp<PolynomialDialect, "exec.univariate_evaluate", [OpPolyUnivariateEvaluate]>;

include "zkc/Interfaces/Mathematical.td"

class PolynomialMathOp<string mnemonic>
    : Op<PolynomialDialect, mnemonic,
         [Pure, DeclareOpInterfaceMethods<MathematicalOpInterface>]> {
  let hasVerifier = 1;
}
def ConstantPolynomialOp : PolynomialMathOp<"constant"> {
  let arguments = (ins Field:$scalar);
  let results = (outs Polynomial:$polynomial);
}
def CoefficientPolynomialOp : PolynomialMathOp<"from_coefficients"> {
  let arguments = (ins FieldArray:$coefficients);
  let results = (outs Polynomial:$polynomial);
}
def MultilinearPolynomialOp : PolynomialMathOp<"mle"> {
  let arguments = (ins FieldArray:$table);
  let results = (outs Polynomial:$polynomial);
}
def AddPolynomialOp : PolynomialMathOp<"add"> {
  let arguments = (ins Polynomial:$lhs, Polynomial:$rhs);
  let results = (outs Polynomial:$polynomial);
}
def MultiplyPolynomialOp : PolynomialMathOp<"multiply"> {
  let arguments = (ins Polynomial:$lhs, Polynomial:$rhs);
  let results = (outs Polynomial:$polynomial);
}
def FixPolynomialOp : PolynomialMathOp<"fix"> {
  let arguments = (ins Polynomial:$input, Variadic<Field>:$prefix);
  let results = (outs Polynomial:$polynomial);
}
def SumPolynomialOp : PolynomialMathOp<"sum_suffix"> {
  let arguments = (ins Polynomial:$input, I64Attr:$count);
  let results = (outs Polynomial:$polynomial);
}
def EvaluatePolynomialOp : PolynomialMathOp<"evaluate"> {
  let arguments = (ins Polynomial:$polynomial, Variadic<Field>:$point);
  let results = (outs Field:$value);
}
def PolynomialCoefficientsOp : PolynomialMathOp<"coefficients"> {
  let arguments = (ins Polynomial:$polynomial);
  let results = (outs FieldArray:$coefficients);
}
def EvaluateDomainOp : PolynomialMathOp<"evaluate_domain"> {
  let arguments = (ins Polynomial:$polynomial, StrArrayAttr:$points);
  let results = (outs FieldArray:$values);
}
def InterpolateDomainOp : PolynomialMathOp<"interpolate"> {
  let arguments = (ins FieldArray:$values, StrArrayAttr:$points);
  let results = (outs Polynomial:$polynomial);
}
def FixTableOp : PolynomialMathOp<"fix_table"> {
  let arguments = (ins FieldArray:$table, Variadic<Field>:$prefix);
  let results = (outs FieldArray:$result);
}

// A ring expression over named factor slots. Its scalar algebra is interpreted
// under polynomial substitution; it is never an executable callback.
def RecipeOp : Op<PolynomialDialect, "recipe", [Symbol, IsolatedFromAbove, SingleBlock]> {
  let arguments = (ins SymbolNameAttr:$sym_name, I64Attr:$degree);
  let regions = (region AnyRegion:$body);
  let hasRegionVerifier = 1;
}
def RecipeYieldOp : Op<PolynomialDialect, "recipe_yield", [Terminator, HasParent<"RecipeOp">]> {
  let arguments = (ins Field:$value);
}
// A checked callable realization of a recipe. Expansion produces ordinary
// local computation, preserving this symbol and its exact signature.
def RealizeOp : Op<PolynomialDialect, "realize", [Symbol, DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let arguments = (ins SymbolNameAttr:$sym_name, FlatSymbolRefAttr:$recipe,
                       StrAttr:$kind, TypeAttrOf<FunctionType>:$function_type);
  let hasVerifier = 1;
}
#endif
