#ifndef ZKC_DIALECT_TYPES_TD
#define ZKC_DIALECT_TYPES_TD
include "zkc/Dialect/Base.td"
// Interactive value types; core finite types remain in IR.td.
def PCSDialect : ZKCDialect {
  let name = "pcs";
  let cppNamespace = "::zkc";
  let useDefaultTypePrinterParser = 1;
}
def Capability : TypeDef<PIRDialect, "Capability"> {
  let mnemonic = "capability";
  let parameters = (ins StringRefParameter<"Installed capability kind">:$kind);
  let assemblyFormat = "`<` $kind `>`";
}
def Variant : TypeDef<PIRDialect, "Variant"> {
  let mnemonic = "variant";
  let parameters = (ins StringRefParameter<"Canonical complete logical descriptor">:$descriptor);
  let assemblyFormat = "`<` $descriptor `>`";
}
def Opaque : TypeDef<PIRDialect, "Opaque"> {
  let mnemonic = "opaque";
  let parameters = (ins StringRefParameter<"Declared data type">:$name);
  let assemblyFormat = "`<` $name `>`";
}
def Multilinear : TypeDef<PolynomialDialect, "Multilinear"> {
  let mnemonic = "multilinear";
  let parameters = (ins StringRefParameter<"Field domain">:$domain);
  let assemblyFormat = "`<` $domain `>`";
}
def Quadratic : TypeDef<PolynomialDialect, "Quadratic"> {
  let mnemonic = "quadratic";
  let parameters = (ins StringRefParameter<"Field domain">:$domain);
  let assemblyFormat = "`<` $domain `>`";
}
def Matrix : TypeDef<AlgebraDialect, "Matrix"> {
  let mnemonic = "matrix";
  let summary = "finite logical matrix over a field, independent of storage";
  let parameters = (ins StringRefParameter<"Field domain">:$domain);
  let assemblyFormat = "`<` $domain `>`";
}
def Group : TypeDef<AlgebraDialect, "Group"> {
  let mnemonic = "group";
  let parameters = (ins StringRefParameter<"Group domain">:$domain);
  let assemblyFormat = "`<` $domain `>`";
}
def Univariate : TypeDef<PolynomialDialect, "Univariate"> {
  let mnemonic = "univariate";
  let summary = "normalized ascending coefficients; zero is the empty polynomial";
  let parameters = (ins StringRefParameter<"Field domain">:$domain);
  let assemblyFormat = "`<` $domain `>`";
}
def PCSObject : TypeDef<PCSDialect, "Object"> {
  let mnemonic = "object";
  let parameters = (ins StringRefParameter<"PCS contract">:$scheme,
    StringRefParameter<"Object kind">:$kind);
  let assemblyFormat = "`<` $scheme `,` $kind `>`";
}

def OracleDialect : ZKCDialect {
  let name = "oracle";
  let cppNamespace = "::zkc";
  let useDefaultTypePrinterParser = 1;
}
def OracleObject : TypeDef<OracleDialect, "OracleObject"> {
  let mnemonic = "object";
  let summary = "nominal row authentication object or ordered custody collection";
  let parameters = (ins StringRefParameter<"Row commitment contract">:$scheme,
    StringRefParameter<"Object kind">:$kind);
  let assemblyFormat = "`<` $scheme `,` $kind `>`";
}
#endif
