#ifndef ZKC_DIALECT_ALGEBRA_IR_ALGEBRAATTRS_TD
#define ZKC_DIALECT_ALGEBRA_IR_ALGEBRAATTRS_TD
include "mlir/IR/AttrTypeBase.td"
include "mlir/IR/EnumAttr.td"
include "zkc/Dialect/Algebra/IR/AlgebraDialect.td"

def AlgebraFieldLiteral : AttrDef<AlgebraDialect, "FieldLiteral"> {
  let mnemonic = "literal";
  let summary = "a canonical field element in its declared presentation";
  let parameters = (ins "::zkc::algebra::FieldType":$field,
    "::mlir::IntegerAttr":$value);
  let assemblyFormat = "`<` $field `,` $value `>`";
  let genVerifyDecl = 1;
}
def AlgebraRingNodeKind : I32EnumAttr<"RingNodeKind", "selected Ring graph node", [
  I32EnumAttrCase<"Constant", 0, "constant">,
  I32EnumAttrCase<"Input", 1, "input">,
  I32EnumAttrCase<"Add", 2, "add">,
  I32EnumAttrCase<"Multiply", 3, "multiply">,
  I32EnumAttrCase<"Negate", 4, "negate">,
  I32EnumAttrCase<"Embed", 5, "embed">
]> {
  let cppNamespace = "::zkc::algebra";
  let genSpecializedAttr = 0;
}
def AlgebraRingNode : AttrDef<AlgebraDialect, "RingNode"> {
  let mnemonic = "ring_node";
  let summary = "one ordered node of an immutable selected Ring graph";
  let parameters = (ins EnumParameter<AlgebraRingNodeKind>:$kind,
    "::mlir::DenseI32ArrayAttr":$indices,
    OptionalParameter<"::zkc::algebra::FieldLiteralAttr">:$literal,
    OptionalParameter<"::zkc::algebra::FieldType">:$target);
  let assemblyFormat = "`<` $kind `,` $indices (`,` $literal^)? (`into` $target^)? `>`";
  let genVerifyDecl = 1;
}
def AlgebraRingExpression : AttrDef<AlgebraDialect, "RingExpression"> {
  let mnemonic = "ring_expression";
  let summary = "exact selected Ring graph, including node order and sharing";
  let parameters = (ins OptionalArrayRefParameter<"::zkc::algebra::FieldType">:$inputs,
    OptionalArrayRefParameter<"::zkc::algebra::RingNodeAttr">:$nodes,
    "::mlir::DenseI32ArrayAttr":$outputs);
  let assemblyFormat = "`<` (`inputs` `[` $inputs^ `]`)? (`nodes` `[` $nodes^ `]`)? `outputs` $outputs `>`";
  let genVerifyDecl = 1;
}
#endif
