#ifndef ZKC_DIALECT_ALGEBRA_IR_ALGEBRAOPS_TD
#define ZKC_DIALECT_ALGEBRA_IR_ALGEBRAOPS_TD

include "zkc/Dialect/Types.td"
include "zkc/Dialect/Algebra/IR/AlgebraAttrs.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "zkc/Interfaces/Mathematical.td"

class TotalMathOp<Dialect dialect, string mnemonic, Type lhs, Type rhs,
                  Type result, list<Trait> traits = []>
    : Op<dialect, mnemonic, !listconcat([Pure], traits)> {
  let arguments = (ins lhs:$lhs, rhs:$rhs);
  let results = (outs result:$value);
  let hasVerifier = 1;
  let assemblyFormat = "$lhs `,` $rhs attr-dict `:` functional-type(operands, results)";
}

def MultilinearRestrictPrefixOp : TotalMathOp<AlgebraDialect,
    "multilinear_restrict_prefix", FieldVector, FieldVector, FieldVector,
    [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;

def FieldAddOp : TotalMathOp<AlgebraDialect, "field_add", Field, Field, Field, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;

def FieldEqualOp : TotalMathOp<AlgebraDialect, "field_equal", Field, Field, I1, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;

def FieldMultiplyOp : TotalMathOp<AlgebraDialect, "field_multiply", Field, Field, Field, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;

def GroupAddOp : TotalMathOp<AlgebraDialect, "group_add", Group, Group, Group, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;

def GroupIdentityOp : Op<AlgebraDialect, "group_identity",
    [Pure, DeclareOpInterfaceMethods<MathematicalOpInterface>]> {
  let summary = "The identity of the result's nominal group";
  let results = (outs Group:$value);
  let hasVerifier = 1;
  let assemblyFormat = "attr-dict `:` type($value)";
}

def GroupEqualOp : TotalMathOp<AlgebraDialect, "group_equal", Group, Group, I1, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;

def GroupScaleOp : TotalMathOp<AlgebraDialect, "group_scale", Group, Field, Group, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;

def ConstantFieldOp : Op<AlgebraDialect, "constant",
                        [Pure, ConstantLike, DeclareOpInterfaceMethods<MathematicalOpInterface>]> {
  let arguments = (ins AlgebraFieldLiteral:$value);
  let results = (outs Field:$result);
  let hasVerifier = 1;
  let hasFolder = 1;
}
def SubtractFieldOp : TotalMathOp<AlgebraDialect, "field_subtract", Field,
    Field, Field, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;

def PairingOp : TotalMathOp<AlgebraDialect, "pairing", Group, Group, Group, [DeclareOpInterfaceMethods<MathematicalOpInterface>]>;


#endif
