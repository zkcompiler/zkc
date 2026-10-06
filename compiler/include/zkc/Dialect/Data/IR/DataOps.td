#ifndef ZKC_DIALECT_DATA_IR_DATAOPS_TD
#define ZKC_DIALECT_DATA_IR_DATAOPS_TD
include "zkc/Dialect/Data/IR/DataDialect.td"
include "zkc/Dialect/Types.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "zkc/Dialect/Kernels.td"
def SequenceEmptyExecOp : KernelOp<DataDialect, "exec.sequence_empty", [OpSequenceEmpty]>;
def SequenceAppendExecOp : KernelOp<DataDialect, "exec.sequence_append", [OpSequenceAppend]>;
def SequenceLengthExecOp : KernelOp<DataDialect, "exec.sequence_length", [OpSequenceLength]>;
def SequenceAtExecOp : KernelOp<DataDialect, "exec.sequence_at", [OpSequenceAt]>;
class DataExpression<string name> : Op<DataDialect, name, [Pure]> {
  let hasVerifier = 1;
}
def Data_SequenceEmptyOp : DataExpression<"sequence_empty"> {
  let results = (outs Sequence:$output);
}
def Data_SequenceAppendOp : DataExpression<"sequence_append"> {
  let arguments = (ins Sequence:$input, AnyType:$element);
  let results = (outs Sequence:$output);
}
def Data_SequenceLengthOp : DataExpression<"sequence_length"> {
  let arguments = (ins Sequence:$input);
  let results = (outs UI64:$output);
}
def Data_IndexOp : DataExpression<"index"> {
  let arguments = (ins StrAttr:$value);
  let results = (outs UI64:$output);
}
def Data_EqualOp : DataExpression<"index_equal"> {
  let arguments = (ins UI64:$lhs, UI64:$rhs);
  let results = (outs I1:$output);
}
def Data_LessOp : DataExpression<"index_less"> {
  let arguments = (ins UI64:$lhs, UI64:$rhs);
  let results = (outs I1:$output);
}
def Data_MakeOp : DataExpression<"make"> {
  let arguments = (ins Variadic<AnyType>:$payload, StrAttr:$alternative);
  let results = (outs Variant:$output);
}
def Data_GetOp : DataExpression<"get"> {
  let arguments = (ins Variant:$input, I64Attr:$index);
  let results = (outs AnyType:$output);
}
def Data_IsOp : DataExpression<"is"> {
  let arguments = (ins Variant:$input, StrAttr:$alternative);
  let results = (outs I1:$output);
}
def Data_DimOp : DataExpression<"dim"> {
  let arguments = (ins AnyRankedTensor:$input, I64Attr:$axis);
  let results = (outs UI64:$output);
}
#endif
