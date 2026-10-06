#ifndef ZKC_DIALECT_CLAIM_IR_CLAIMTYPES_TD
#define ZKC_DIALECT_CLAIM_IR_CLAIMTYPES_TD

include "mlir/IR/AttrTypeBase.td"
include "zkc/Dialect/Claim/IR/ClaimDialect.td"

def ClaimEvidence : TypeDef<ClaimDialect, "ClaimEvidence"> {
  let mnemonic = "evidence";
}

def ClaimPending : TypeDef<ClaimDialect, "ClaimPending"> {
  let mnemonic = "pending";
}

#endif
