#ifndef ZKC_DIALECT_RELATION_TD
#define ZKC_DIALECT_RELATION_TD
include "mlir/IR/SymbolInterfaces.td"
include "zkc/Dialect/Base.td"

def RelationDialect : ZKCDialect {
  let name = "relation";
  let cppNamespace = "::zkc";
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

#endif
