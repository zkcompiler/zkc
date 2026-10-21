#ifndef ZKC_DIALECT_ENTRY_IR_ENTRYTYPES_TD
#define ZKC_DIALECT_ENTRY_IR_ENTRYTYPES_TD
include "zkc/Dialect/Entry/IR/EntryDialect.td"
include "mlir/IR/AttrTypeBase.td"
def EntryValue : TypeDef<EntryDialect, "Value"> {
  let mnemonic = "value";
  let parameters = (ins StringRefParameter<"Canonical logical schema">:$schema);
  let assemblyFormat = "`<` $schema `>`";
}
#endif
