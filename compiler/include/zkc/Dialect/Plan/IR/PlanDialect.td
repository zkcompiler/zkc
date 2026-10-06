#ifndef ZKC_DIALECT_PLAN_IR_PLANDIALECT_TD
#define ZKC_DIALECT_PLAN_IR_PLANDIALECT_TD

include "zkc/Dialect/Base.td"

def PlanDialect : ZKCDialect {
  let name = "plan";
  let cppNamespace = "::zkc::plan";
  let useDefaultTypePrinterParser = 1;
}

#endif
