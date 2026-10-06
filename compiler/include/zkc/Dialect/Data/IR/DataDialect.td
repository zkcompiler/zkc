#ifndef ZKC_DIALECT_DATA_IR_DATADIALECT_TD
#define ZKC_DIALECT_DATA_IR_DATADIALECT_TD
include "zkc/Dialect/Base.td"
def DataDialect : ZKCDialect {
  let name = "data";
  let cppNamespace = "::zkc::data";
  let useDefaultTypePrinterParser = 1;
}
#endif
