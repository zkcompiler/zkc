#ifndef ZKC_DIALECT_CLAIM_IR_CLAIMDIALECT_TD
#define ZKC_DIALECT_CLAIM_IR_CLAIMDIALECT_TD

include "zkc/Dialect/Base.td"

def ClaimDialect : ZKCDialect {
  let name = "claim";
  let cppNamespace = "::zkc::claim";
  let useDefaultTypePrinterParser = 1;
  let description = [{
    Optional execution-bound analysis, checked relative to independently
    retained source and contracts. These operations never execute protocols.
    A pending proposition is not truth. Evidence is reusable logical data;
    it cannot issue, duplicate or advance runtime resources. Body laws remain
    explicit caller trust premises. No logical erasure removes PIR checks.
  }];
}

#endif
