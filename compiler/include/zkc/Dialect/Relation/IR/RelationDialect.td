#ifndef ZKC_DIALECT_RELATION_IR_RELATIONDIALECT_TD
#define ZKC_DIALECT_RELATION_IR_RELATIONDIALECT_TD

include "zkc/Dialect/Base.td"

def RelationDialect : ZKCDialect {
  let name = "relation";
  let cppNamespace = "::zkc::relation";
}

#endif
