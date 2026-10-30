#ifndef ZKC_DIALECT_DATA_IR_DATAATTRS_TD
#define ZKC_DIALECT_DATA_IR_DATAATTRS_TD
include "mlir/IR/AttrTypeBase.td"
include "zkc/Dialect/Data/IR/DataDialect.td"
def NominalIdentity : AttrDef<DataDialect, "Identity"> {
  let mnemonic = "identity";
  let summary = "complete structural nominal identity, including phantom actuals";
  let parameters = (ins "::mlir::ArrayAttr":$term);
  let assemblyFormat = "`<` $term `>`";
  let genVerifyDecl = 1;
}
def VariantAlternative : AttrDef<DataDialect, "Alternative"> {
  let mnemonic = "alternative";
  let parameters = (ins "::mlir::StringAttr":$label,
    OptionalArrayRefParameter<"::mlir::Type">:$payload);
  let assemblyFormat = "`<` $label (`,` `[` $payload^ `]`)? `>`";
  let genVerifyDecl = 1;
}
def LogicalLayoutField : AttrDef<DataDialect, "LayoutField"> {
  let mnemonic = "layout_field";
  let parameters = (ins "::mlir::StringAttr":$name, "uint64_t":$offset,
    "::zkc::data::LayoutAttr":$layout);
  let assemblyFormat = "`<` $name `,` $offset `,` $layout `>`";
  let genVerifyDecl = 1;
}
def LogicalLayoutAlternative : AttrDef<DataDialect, "LayoutAlternative"> {
  let mnemonic = "layout_alternative";
  let parameters = (ins "::mlir::StringAttr":$name,
    OptionalArrayRefParameter<"::zkc::data::LayoutFieldAttr">:$fields);
  let assemblyFormat = "`<` $name (`,` `[` $fields^ `]`)? `>`";
  let genVerifyDecl = 1;
}
def LogicalLayout : AttrDef<DataDialect, "Layout"> {
  let mnemonic = "layout";
  // Child layouts are shared structurally. Aliases keep their assembly nesting
  // independent of source schema depth without relaxing parser resource limits.
  let genMnemonicAlias = 1;
  let summary = "complete source value layout with ordered typed children";
  let parameters = (ins "::mlir::StringAttr":$kind,
    "::mlir::StringAttr":$identity, "::mlir::StringAttr":$displayType,
    "bool":$custody, "bool":$constructible, "bool":$copy, "bool":$drop,
    OptionalArrayRefParameter<"::zkc::data::LayoutFieldAttr">:$fields,
    OptionalArrayRefParameter<"::zkc::data::LayoutAlternativeAttr">:$alternatives,
    OptionalArrayRefParameter<"::mlir::Type">:$leaves);
  let assemblyFormat = [{
    `<` $kind `,` $identity `,` $displayType `,`
        $custody `,` $constructible `,` $copy `,` $drop
        (`fields` `[` $fields^ `]`)?
        (`alternatives` `[` $alternatives^ `]`)?
        (`leaves` `[` $leaves^ `]`)? `>`
  }];
  let genVerifyDecl = 1;
}
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
