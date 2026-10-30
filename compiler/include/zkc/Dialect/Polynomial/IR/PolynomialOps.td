#ifndef ZKC_DIALECT_POLYNOMIAL_IR_POLYNOMIALOPS_TD
#define ZKC_DIALECT_POLYNOMIAL_IR_POLYNOMIALOPS_TD

include "zkc/Dialect/Types.td"
include "zkc/Dialect/Algebra/IR/AlgebraAttrs.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"

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
  let arguments = (ins Polynomial:$polynomial, AlgebraFieldLiterals:$points);
  let results = (outs FieldArray:$values);
}
def InterpolateDomainOp : PolynomialMathOp<"interpolate"> {
  let arguments = (ins FieldArray:$values, AlgebraFieldLiterals:$points);
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
// Partial ordered realizations of the negacyclic quotient contracts.

// Projection is total reduction. Executable canonical admission is a separate
// ordered contract; quotient values themselves carry no field cancellation law.
def ProjectQuotientOp : Op<PolynomialDialect, "quotient_project",
    [Pure, DeclareOpInterfaceMethods<MathematicalOpInterface>]> {
  let arguments = (ins Indices:$coefficients);
  let results = (outs Quotient:$value);
  let assemblyFormat = "$coefficients attr-dict `:` functional-type(operands, results)";
}
def ObserveQuotientOp : Op<PolynomialDialect, "quotient_coefficients",
    [Pure, DeclareOpInterfaceMethods<MathematicalOpInterface>]> {
  let arguments = (ins Quotient:$value);
  let results = (outs Indices:$coefficients);
  let assemblyFormat = "$value attr-dict `:` functional-type(operands, results)";
}
class QuotientBinaryOp<string mnemonic> : PolynomialMathOp<mnemonic> {
  let arguments = (ins Quotient:$lhs, Quotient:$rhs);
  let results = (outs Quotient:$value);
  let assemblyFormat = "$lhs `,` $rhs attr-dict `:` functional-type(operands, results)";
}
def AddQuotientOp : QuotientBinaryOp<"quotient_add">;
def SubtractQuotientOp : QuotientBinaryOp<"quotient_subtract">;
def MultiplyQuotientOp : QuotientBinaryOp<"quotient_multiply">;

#endif
