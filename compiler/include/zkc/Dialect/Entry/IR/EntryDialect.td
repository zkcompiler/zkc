#ifndef ZKC_DIALECT_ENTRY_IR_ENTRYDIALECT_TD
#define ZKC_DIALECT_ENTRY_IR_ENTRYDIALECT_TD
include "zkc/Dialect/Base.td"
def EntryDialect : ZKCDialect {
  let name = "entry";
  let cppNamespace = "::zkc::entry";
  let useDefaultTypePrinterParser = 1;
}
#endif
