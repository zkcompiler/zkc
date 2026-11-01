#ifndef ZKC_DIALECT_RESIDUE_IR_RESIDUETYPES_TD
#define ZKC_DIALECT_RESIDUE_IR_RESIDUETYPES_TD
include "mlir/IR/AttrTypeBase.td"
include "zkc/Dialect/Residue/IR/ResidueDialect.td"
def ResidueValue : TypeDef<ResidueDialect, "Value"> {
  let mnemonic = "value";
  let summary = "canonical integer residue with an explicit unsigned word modulus";
  let parameters = (ins "::mlir::IntegerAttr":$modulus);
  let assemblyFormat = "`<` $modulus `>`";
  let genVerifyDecl = 1;
  let extraClassDeclaration = [{
    unsigned getWidth() const { return getModulus().getValue().getBitWidth(); }
  }];
}
#endif
