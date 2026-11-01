#ifndef ZKC_DIALECT_RESIDUE_IR_RESIDUEOPS_TD
#define ZKC_DIALECT_RESIDUE_IR_RESIDUEOPS_TD
include "zkc/Dialect/Residue/IR/ResidueTypes.td"
include "zkc/Dialect/Residue/IR/ResidueAttrs.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"

def ResidueConstantOp : Op<ResidueDialect, "constant", [Pure, ConstantLike]> {
  let arguments = (ins ResidueLiteral:$value);
  let results = (outs ResidueValue:$result);
  let hasVerifier = 1;
  let hasFolder = 1;
}
class ResidueBinary<string name> : Op<ResidueDialect, name,
    [Pure, SameOperandsAndResultType, Elementwise, Scalarizable, Tensorizable]> {
  let arguments = (ins AnyType:$lhs, AnyType:$rhs);
  let results = (outs AnyType:$result);
  let assemblyFormat = "$lhs `,` $rhs attr-dict `:` type($result)";
  let hasVerifier = 1;
  let hasFolder = 1;
}
def ResidueAddOp : ResidueBinary<"add">;
def ResidueSubtractOp : ResidueBinary<"subtract">;
def ResidueMultiplyOp : ResidueBinary<"multiply">;
class ResidueConversion<string name> : Op<ResidueDialect, name,
    [Pure, Elementwise, Scalarizable, Tensorizable]> {
  let arguments = (ins AnyType:$input);
  let results = (outs AnyType:$result);
  let assemblyFormat = "$input attr-dict `:` type($input) `to` type($result)";
  let hasVerifier = 1;
  let hasFolder = 1;
}
def ResidueProjectOp : ResidueConversion<"project">;
def ResidueLiftOp : ResidueConversion<"lift">;
def ResidueCenteredLiftOp : ResidueConversion<"centered_lift">;
#endif
