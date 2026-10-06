#ifndef ZKC_DIALECT_ALGEBRA_IR_ALGEBRADIALECT_TD
#define ZKC_DIALECT_ALGEBRA_IR_ALGEBRADIALECT_TD

include "zkc/Dialect/Base.td"

def AlgebraDialect : ZKCDialect {
  let name = "algebra";
  let cppNamespace = "::zkc::algebra";
  let useDefaultTypePrinterParser = 1;
}

#endif
