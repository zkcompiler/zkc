#ifndef ZKC_DIALECT_COMMITMENT_IR_COMMITMENTDIALECT_TD
#define ZKC_DIALECT_COMMITMENT_IR_COMMITMENTDIALECT_TD

include "zkc/Dialect/Base.td"

def CommitmentDialect : ZKCDialect {
  let name = "commitment";
  let cppNamespace = "::zkc::commitment";
  let useDefaultTypePrinterParser = 1;
}

#endif
