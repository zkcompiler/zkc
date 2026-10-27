#ifndef ZKC_DIALECT_RUNTIME_IR_RUNTIMEDIALECT_TD
#define ZKC_DIALECT_RUNTIME_IR_RUNTIMEDIALECT_TD
include "zkc/Dialect/Base.td"
def RuntimeDialect : ZKCDialect {
  let name = "runtime";
  let cppNamespace = "::zkc::runtime";
  let useDefaultTypePrinterParser = 1;
}
#endif
