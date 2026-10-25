#ifndef ZKC_DIALECT_EXEC_IR_EXECDIALECT_TD
#define ZKC_DIALECT_EXEC_IR_EXECDIALECT_TD
include "zkc/Dialect/Base.td"
def ExecDialect : ZKCDialect {
  let name = "exec";
  let cppNamespace = "::zkc::exec";
  let useDefaultTypePrinterParser = 1;
}
#endif
