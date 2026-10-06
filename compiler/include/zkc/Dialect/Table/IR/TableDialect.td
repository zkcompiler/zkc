#ifndef ZKC_DIALECT_TABLE_IR_TABLEDIALECT_TD
#define ZKC_DIALECT_TABLE_IR_TABLEDIALECT_TD

include "zkc/Dialect/Base.td"

def TableDialect : ZKCDialect {
  let name = "table";
  let cppNamespace = "::zkc::table";
  let useDefaultTypePrinterParser = 1;
}

#endif
