#ifndef ZKC_DIALECT_RELATION_IR_RELATIONOPS_TD
#define ZKC_DIALECT_RELATION_IR_RELATIONOPS_TD

include "zkc/Dialect/Types.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "zkc/Dialect/BoundOperations.td"

def AIRRelationOp : Op<RelationDialect, "air", [Symbol]> {
  let summary = "Finite arithmetic trace constraints with explicit row scopes";
  let description = [{
    Immutable expression arenas retain constants, public inputs, relative reads
    and arithmetic. Constraints retain first, last, every or noncyclic transition
    scope. Read windows and degree are derived, not supplied as trusted facts.
    This declaration does not select a polynomial domain or a STARK prover.
  }];
  let arguments = (ins SymbolNameAttr:$sym_name, StrAttr:$field,
    I64Attr:$columns, I64Attr:$public_inputs, ArrayAttr:$constraints);
  let hasVerifier = 1;
  let assemblyFormat = "$sym_name attr-dict";
}

def R1CSRelationOp : Op<RelationDialect, "r1cs", [Symbol]> {
  let summary = "Immutable rank-one constraints and their statement layout";
  let description = [{
    Assignment columns are ONE, public outputs, public inputs, then private
    witness. Each constraint has three sparse linear forms; entries are
    (column, canonical field coefficient) pairs in strictly increasing column
    order with nonzero coefficients. The relation additionally fixes ONE and
    the public prefix. This declaration is not a witness generator or prover.
    It may be analyzed before specializing its mathematical views into PIR.
  }];
  let arguments = (ins SymbolNameAttr:$sym_name, StrAttr:$field,
    I64Attr:$columns, I64Attr:$public_outputs, I64Attr:$public_inputs,
    ArrayAttr:$constraints);
  let hasVerifier = 1;
  let assemblyFormat = "$sym_name attr-dict";
}

// Dense assertion residuals of one present table of an admitted relation
// bundle asset. The bundle body is admitted by the Host under the digest
// parameter; the compiler checks the contract and the digest reference.
def TableRowsOp : BoundOp<RelationDialect, "exec.table_rows", [OpRelationTableRows]>;
// Polynomial view of one present table of an admitted relation bundle asset:
// derived shape, input descriptors, assertion scopes and point substitutions.
// The compiler checks static table and carrier premises; actual heights
// are checked when the height-taking kernels execute.
def TableShapeOp : BoundOp<RelationDialect, "exec.table_shape", [OpRelationTableShape]>;
def TableInputOp : BoundOp<RelationDialect, "exec.table_input", [OpRelationTableInput]>;
def TableScopeOp : BoundOp<RelationDialect, "exec.table_scope", [OpRelationTableScope]>;
def TablePointOp : BoundOp<RelationDialect, "exec.table_point", [OpRelationTablePoint]>;
def TablePointsOp : BoundOp<RelationDialect, "exec.table_points", [OpRelationTablePoints]>;
// Metadata and interaction view of one table of an admitted Bundle: widths,
// declared height policy, interaction descriptors and record substitutions.
// The compiler checks static table and carrier premises. Height-taking
// kernels check their actual height at execution; metadata and substitutions
// require no domain.
def TableWidthsOp : BoundOp<RelationDialect, "exec.table_widths", [OpRelationTableWidths]>;
def TablePolicyOp : BoundOp<RelationDialect, "exec.table_policy", [OpRelationTablePolicy]>;
def TableInteractionsOp : BoundOp<RelationDialect, "exec.table_interactions", [OpRelationTableInteractions]>;
def TableInteractionOp : BoundOp<RelationDialect, "exec.table_interaction", [OpRelationTableInteraction]>;
def TableRecordPointsOp : BoundOp<RelationDialect, "exec.table_record_points", [OpRelationTableRecordPoints]>;

// A predicate declaration. A formula reference is metadata, not a call.
def DeclareOp : Op<RelationDialect, "declare", [Symbol,
    DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let summary = "Relation identity, input purposes and optional Math definition";
  let arguments = (ins SymbolNameAttr:$sym_name,
    OptionalAttr<StrAttr>:$sym_visibility,
    StrAttr:$kind, StrAttr:$key, StrAttr:$revision,
    DefaultValuedAttr<ArrayAttr, "{}">:$static_arguments,
    TypeAttrOf<FunctionType>:$signature, StrArrayAttr:$purposes,
    OptionalAttr<FlatSymbolRefAttr>:$formula);
  let hasVerifier = 1;
  let assemblyFormat = "$sym_name attr-dict";
}

#endif
