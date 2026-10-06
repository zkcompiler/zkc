#ifndef ZKC_DIALECT_POLYNOMIAL_IR_POLYNOMIALDIALECT_TD
#define ZKC_DIALECT_POLYNOMIAL_IR_POLYNOMIALDIALECT_TD

include "zkc/Dialect/Base.td"

def PolynomialDialect : ZKCDialect {
  let name = "poly";
  let cppNamespace = "::zkc::poly";
  let useDefaultTypePrinterParser = 1;
}

#endif
