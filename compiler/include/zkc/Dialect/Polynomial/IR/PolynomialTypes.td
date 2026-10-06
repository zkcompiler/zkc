#ifndef ZKC_DIALECT_POLYNOMIAL_IR_POLYNOMIALTYPES_TD
#define ZKC_DIALECT_POLYNOMIAL_IR_POLYNOMIALTYPES_TD

include "mlir/IR/AttrTypeBase.td"
include "zkc/Dialect/Polynomial/IR/PolynomialDialect.td"

class Shaped<string name, string spelling> : TypeDef<PolynomialDialect, name> {
  let mnemonic = spelling;
  let summary = "shaped polynomial value";
  let parameters = (ins StringRefParameter<"Resolved field">:$domain,
      StringRefParameter<"Original natural rank">:$rank);
  let assemblyFormat = "`<` $domain `,` $rank `>`";
  let genVerifyDecl = 1;
}

def Multilinear : TypeDef<PolynomialDialect, "Multilinear"> {
  let mnemonic = "multilinear";
  let parameters = (ins StringRefParameter<"Field domain">:$domain);
  let assemblyFormat = "`<` $domain `>`";
}

def Point : TypeDef<PolynomialDialect, "Point"> {
  let mnemonic = "point";
  let summary = "polynomial point";
  let parameters = (ins StringRefParameter<"Resolved field">:$domain);
  let assemblyFormat = "`<` $domain `>`";
  let genVerifyDecl = 1;
}

def Quadratic : TypeDef<PolynomialDialect, "Quadratic"> {
  let mnemonic = "quadratic";
  let parameters = (ins StringRefParameter<"Field domain">:$domain);
  let assemblyFormat = "`<` $domain `>`";
}

def Residual : Shaped<"Residual", "residual">;

def Table : Shaped<"Table", "table">;

def Univariate : TypeDef<PolynomialDialect, "Univariate"> {
  let mnemonic = "univariate";
  let summary = "normalized ascending coefficients; zero is the empty polynomial";
  let parameters = (ins StringRefParameter<"Field domain">:$domain);
  let assemblyFormat = "`<` $domain `>`";
}

// Formal multivariate expressions have no executable value encoding. The
// existing Univariate type separately denotes a concrete coefficient value.
def Polynomial : TypeDef<PolynomialDialect, "Polynomial"> {
  let mnemonic = "polynomial";
  let summary = "formal polynomial over a field and ordered variables";
  let parameters = (ins StringRefParameter<"Field domain">:$domain,
                        "uint64_t":$arity);
  let assemblyFormat = "`<` $domain `,` $arity `>`";
  let genVerifyDecl = 1;
}

#endif
