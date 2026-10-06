#ifndef ZKC_DIALECT_CRYPTO_IR_CRYPTODIALECT_TD
#define ZKC_DIALECT_CRYPTO_IR_CRYPTODIALECT_TD

include "zkc/Dialect/Base.td"

def CryptoDialect : ZKCDialect {
  let name = "crypto";
  let cppNamespace = "::zkc::crypto";
}

#endif
