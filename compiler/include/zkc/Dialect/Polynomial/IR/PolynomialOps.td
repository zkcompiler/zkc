#ifndef ZKC_DIALECT_POLYNOMIAL_IR_POLYNOMIALOPS_TD
#define ZKC_DIALECT_POLYNOMIAL_IR_POLYNOMIALOPS_TD

include "zkc/Dialect/Types.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "zkc/Dialect/Kernels.td"

def AppendPointOp : KernelOp<PolynomialDialect, "exec.append_point", [OpPolyAppendPoint]>;

def BoundaryOp : KernelOp<PolynomialDialect, "exec.boundary", [OpPolyBoundary]>;

def CoefficientCountOp : KernelOp<PolynomialDialect, "exec.coefficient_count", [OpPolyCoefficientCount]>;

def CoefficientsOp : KernelOp<PolynomialDialect, "exec.coefficients", [OpPolyCoefficients]>;

def CosetEvaluateOp : KernelOp<PolynomialDialect, "exec.coset_evaluate", [OpPolyCosetEvaluate]>;

def CosetInterpolateOp : KernelOp<PolynomialDialect, "exec.coset_interpolate", [OpPolyCosetInterpolate]>;

def DegreeCheckOp : KernelOp<PolynomialDialect, "exec.degree_check", [OpPolyDegreeCheck]>;

def DivideOpeningOp : KernelOp<PolynomialDialect, "exec.divide_opening", [OpPolyDivideOpening]>;

def DomainPointOp : KernelOp<PolynomialDialect, "exec.domain_point", [OpPolyDomainPoint]>;

def DomainPointsOp : KernelOp<PolynomialDialect, "exec.domain_points", [OpPolyDomainPoints]>;

def DomainRootOp : KernelOp<PolynomialDialect, "exec.domain_root", [OpPolyDomainRoot]>;

def EmptyPointOp : KernelOp<PolynomialDialect, "exec.empty_point", [OpPolyEmptyPoint]>;

def EqualityWeightsOp : KernelOp<PolynomialDialect, "exec.equality_weights", [OpPolyEqualityWeights]>;

def EvenOddFoldOp : KernelOp<PolynomialDialect, "exec.even_odd_fold", [OpPolyEvenOddFold]>;

def FoldOp : KernelOp<PolynomialDialect, "exec.fold", [OpPolyFold]>;

def FromCoefficientsOp : KernelOp<PolynomialDialect, "exec.from_coefficients", [OpPolyFromCoefficients]>;

def MLEEvaluateOp : KernelOp<PolynomialDialect, "exec.mle_evaluate", [OpPolyEvaluate]>;

def OpeningQuotientOp : KernelOp<PolynomialDialect, "exec.opening_quotient", [OpPolyOpeningQuotient]>;

def PointFromVectorOp : KernelOp<PolynomialDialect, "exec.point_from_vector", [OpVectorToPoint]>;

def PointToVectorOp : KernelOp<PolynomialDialect, "exec.point_to_vector", [OpVectorFromPoint]>;

def ProductRoundOp : KernelOp<PolynomialDialect, "exec.product_round", [OpPolyProductRound]>;

def ProductSumOp : KernelOp<PolynomialDialect, "exec.product_sum", [OpPolyProductSum]>;

def RoundEvaluateOp : KernelOp<PolynomialDialect, "exec.round_evaluate", [OpPolyRoundEvaluate]>;

def TableArityOp : KernelOp<PolynomialDialect, "exec.table_arity", [OpPolyTableArity]>;

def TableFromVectorOp : KernelOp<PolynomialDialect, "exec.table_from_vector", [OpVectorToTable]>;

def TableToVectorOp : KernelOp<PolynomialDialect, "exec.table_to_vector", [OpVectorFromTable]>;

def UnivariateBoundaryOp : KernelOp<PolynomialDialect, "exec.univariate_boundary", [OpPolyUnivariateBoundary]>;

def UnivariateEvaluateOp : KernelOp<PolynomialDialect, "exec.univariate_evaluate", [OpPolyUnivariateEvaluate]>;

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
  let arguments = (ins AnyRankedTensor:$coefficients);
  let results = (outs Polynomial:$polynomial);
}
def MultilinearPolynomialOp : PolynomialMathOp<"mle"> {
  let arguments = (ins AnyRankedTensor:$table);
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
  let results = (outs AnyRankedTensor:$coefficients);
}
def EvaluateDomainOp : PolynomialMathOp<"evaluate_domain"> {
  let arguments = (ins Polynomial:$polynomial, StrArrayAttr:$points);
  let results = (outs AnyRankedTensor:$values);
}
def InterpolateDomainOp : PolynomialMathOp<"interpolate"> {
  let arguments = (ins AnyRankedTensor:$values, StrArrayAttr:$points);
  let results = (outs Polynomial:$polynomial);
}
def FixTableOp : PolynomialMathOp<"fix_table"> {
  let arguments = (ins AnyRankedTensor:$table, Variadic<Field>:$prefix);
  let results = (outs AnyRankedTensor:$result);
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
