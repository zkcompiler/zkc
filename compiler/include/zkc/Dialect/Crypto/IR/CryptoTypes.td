#ifndef ZKC_DIALECT_CRYPTO_IR_CRYPTOTYPES_TD
#define ZKC_DIALECT_CRYPTO_IR_CRYPTOTYPES_TD
include "mlir/IR/AttrTypeBase.td"
include "zkc/Dialect/Crypto/IR/CryptoDialect.td"
def Shake128State : TypeDef<CryptoDialect, "Shake128State"> {
  let mnemonic = "shake128_state";
  let summary = "immutable non-wire SHAKE128 absorb/read snapshot";
  let assemblyFormat = "";
}
#endif
