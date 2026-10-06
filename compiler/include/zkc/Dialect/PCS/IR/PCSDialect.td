#ifndef ZKC_DIALECT_PCS_IR_PCSDIALECT_TD
#define ZKC_DIALECT_PCS_IR_PCSDIALECT_TD

include "zkc/Dialect/Base.td"

def PCSDialect : ZKCDialect {
  let name = "pcs";
  let cppNamespace = "::zkc::pcs";
  let useDefaultTypePrinterParser = 1;
}

#endif
