#ifndef ZKC_DIALECT_LOCAL_IR_LOCALDIALECT_TD
#define ZKC_DIALECT_LOCAL_IR_LOCALDIALECT_TD

include "zkc/Dialect/Base.td"

def LocalDialect : ZKCDialect {
  let name = "local";
  let cppNamespace = "::zkc::local";
}

#endif
