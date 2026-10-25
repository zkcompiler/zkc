#ifndef ZKC_DIALECT_COMMITMENT_IR_COMMITMENTTYPES_TD
#define ZKC_DIALECT_COMMITMENT_IR_COMMITMENTTYPES_TD

include "mlir/IR/AttrTypeBase.td"
include "zkc/Dialect/Commitment/IR/CommitmentDialect.td"

def PolynomialObject : TypeDef<CommitmentDialect, "PolynomialObject"> {
  let mnemonic = "polynomial";
  let parameters = (ins StringRefParameter<"PCS contract">:$scheme,
    StringRefParameter<"Object kind">:$kind);
  let assemblyFormat = "`<` $scheme `,` $kind `>`";
}

def VectorObject : TypeDef<CommitmentDialect, "VectorObject"> {
  let mnemonic = "vector";
  let summary = "nominal row authentication object or ordered custody collection";
  let parameters = (ins StringRefParameter<"Row commitment contract">:$scheme,
    StringRefParameter<"Object kind">:$kind);
  let assemblyFormat = "`<` $scheme `,` $kind `>`";
}

#endif
