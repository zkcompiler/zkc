#ifndef ZKC_DIALECT_DATA_IR_DATAATTRS_TD
#define ZKC_DIALECT_DATA_IR_DATAATTRS_TD
include "mlir/IR/AttrTypeBase.td"
include "zkc/Dialect/Data/IR/DataDialect.td"
def IndexBound : AttrDef<DataDialect, "IndexBound"> {
  let mnemonic = "index_bound";
  let parameters = (ins "unsigned":$indexArg, "unsigned":$containerArg, "unsigned":$axis);
  let assemblyFormat = "`<` $indexArg `,` $containerArg `,` $axis `>`";
}
def EqualExtent : AttrDef<DataDialect, "EqualExtent"> {
  let mnemonic = "equal_extent";
  let parameters = (ins "unsigned":$leftArg, "unsigned":$leftAxis,
    "unsigned":$rightArg, "unsigned":$rightAxis);
  let assemblyFormat = "`<` $leftArg `,` $leftAxis `,` $rightArg `,` $rightAxis `>`";
}
#endif
