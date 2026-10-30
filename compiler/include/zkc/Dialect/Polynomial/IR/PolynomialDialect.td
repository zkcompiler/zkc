#ifndef ZKC_DIALECT_POLYNOMIAL_IR_POLYNOMIALDIALECT_TD
#define ZKC_DIALECT_POLYNOMIAL_IR_POLYNOMIALDIALECT_TD

include "zkc/Dialect/Base.td"

def PolynomialDialect : ZKCDialect {
  let name = "poly";
  let cppNamespace = "::zkc::poly";
  // Verification derives Algebra field types and Data residual-state types.
  let dependentDialects = ["::zkc::algebra::AlgebraDialect",
                           "::zkc::data::DataDialect"];
  let useDefaultTypePrinterParser = 1;
}

#endif
