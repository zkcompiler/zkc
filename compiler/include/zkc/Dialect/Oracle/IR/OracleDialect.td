#ifndef ZKC_DIALECT_ORACLE_IR_ORACLEDIALECT_TD
#define ZKC_DIALECT_ORACLE_IR_ORACLEDIALECT_TD

include "zkc/Dialect/Base.td"

def OracleDialect : ZKCDialect {
  let name = "oracle";
  let cppNamespace = "::zkc::oracle";
  let useDefaultTypePrinterParser = 1;
}

#endif
