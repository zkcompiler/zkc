#ifndef ZKC_DIALECT_RELATION_IR_RELATIONOPS_TD
#define ZKC_DIALECT_RELATION_IR_RELATIONOPS_TD

include "zkc/Dialect/Types.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "zkc/Dialect/Kernels.td"

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
def TableRowsOp : KernelOp<RelationDialect, "exec.table_rows", [OpRelationTableRows]>;
// Polynomial view of one present table of an admitted relation bundle asset:
// derived shape, input descriptors, assertion scopes and point substitutions.
// The compiler checks the static table, carrier and height premises.
def TableShapeOp : KernelOp<RelationDialect, "exec.table_shape", [OpRelationTableShape]>;
def TableInputOp : KernelOp<RelationDialect, "exec.table_input", [OpRelationTableInput]>;
def TableScopeOp : KernelOp<RelationDialect, "exec.table_scope", [OpRelationTableScope]>;
def TablePointOp : KernelOp<RelationDialect, "exec.table_point", [OpRelationTablePoint]>;
def TablePointsOp : KernelOp<RelationDialect, "exec.table_points", [OpRelationTablePoints]>;
// Interaction view of one table of an admitted relation bundle asset: the
// declared height policy, interaction descriptors and record substitutions.
// The compiler checks the static table and carrier premises, and for the
// height-taking and record kernels the two-adic height premise.
def TablePolicyOp : KernelOp<RelationDialect, "exec.table_policy", [OpRelationTablePolicy]>;
def TableInteractionsOp : KernelOp<RelationDialect, "exec.table_interactions", [OpRelationTableInteractions]>;
def TableInteractionOp : KernelOp<RelationDialect, "exec.table_interaction", [OpRelationTableInteraction]>;
def TableRecordPointsOp : KernelOp<RelationDialect, "exec.table_record_points", [OpRelationTableRecordPoints]>;

// A supplied predicate contract. It has no callable interface or body.
def DeclareOp : Op<RelationDialect, "declare", [Symbol]> {
  let summary = "External relation identity and ordered logical input purposes";
  let arguments = (ins SymbolNameAttr:$sym_name,
    OptionalAttr<StrAttr>:$sym_visibility,
    StrAttr:$kind, StrAttr:$key, StrAttr:$revision,
    TypeAttrOf<FunctionType>:$signature, StrArrayAttr:$purposes);
  let hasVerifier = 1;
  let assemblyFormat = "$sym_name attr-dict";
}

#endif
