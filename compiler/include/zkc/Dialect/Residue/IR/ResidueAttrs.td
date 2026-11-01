#ifndef ZKC_DIALECT_RESIDUE_IR_RESIDUEATTRS_TD
#define ZKC_DIALECT_RESIDUE_IR_RESIDUEATTRS_TD
include "mlir/IR/AttrTypeBase.td"
include "mlir/IR/BuiltinAttributeInterfaces.td"
include "zkc/Dialect/Residue/IR/ResidueDialect.td"
def ResidueLiteral : AttrDef<ResidueDialect, "Literal", [TypedAttrInterface]> {
  let mnemonic = "literal";
  let summary = "one canonical residue in its exact modulus and word width";
  let parameters = (ins "::zkc::residue::ValueType":$residue,
                       "::mlir::IntegerAttr":$value);
  let assemblyFormat = "`<` $residue `,` $value `>`";
  let genVerifyDecl = 1;
  let extraClassDeclaration = [{
    ::mlir::Type getType() const { return getResidue(); }
  }];
}
#endif
