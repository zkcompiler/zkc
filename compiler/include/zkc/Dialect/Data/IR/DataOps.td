#ifndef ZKC_DIALECT_DATA_IR_DATAOPS_TD
#define ZKC_DIALECT_DATA_IR_DATAOPS_TD
include "zkc/Dialect/Data/IR/DataDialect.td"
include "zkc/Dialect/Types.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "zkc/Dialect/BoundOperations.td"
include "zkc/Interfaces/Mathematical.td"
include "mlir/IR/SymbolInterfaces.td"

def Data_DomainOp : Op<DataDialect, "domain", [Symbol, IsolatedFromAbove, SingleBlock]> {
  let arguments = (ins SymbolNameAttr:$sym_name, StrAttr:$sym_visibility,
    TypeAttrOf<FunctionType>:$function_type);
  let regions = (region AnyRegion:$body);
  let hasRegionVerifier = 1;
}
// Every constructor contributes an ordered admission obligation, even when its
// descriptor is unused. Leave effects unknown and provide no speculation
// interface: NoMemoryEffect would allow generic DCE/CSE to discard admission.
// This is a conservative transformation contract, not a heap allocation effect.
class DomainConstructor<string name> : Op<DataDialect, name> {
  let results = (outs Domain:$output);
  let hasVerifier = 1;
}
def Data_DomainElementsOp : DomainConstructor<"domain_elements"> {
  let arguments = (ins AnyType:$input);
}
def Data_DomainIndicesOp : DomainConstructor<"domain_indices"> {
  let arguments = (ins AnyType:$input, I64Attr:$axis);
}
def Data_DomainRangeOp : DomainConstructor<"domain_range"> {
  let arguments = (ins UI64:$lower, UI64:$upper);
}
def Data_DomainZipOp : DomainConstructor<"domain_zip"> {
  let arguments = (ins Variadic<Domain>:$inputs);
}
def Data_DomainProductOp : DomainConstructor<"domain_product"> {
  let arguments = (ins Variadic<Domain>:$inputs);
}
def Data_DomainMatrixRowOp : DomainConstructor<"domain_matrix_row"> {
  let arguments = (ins FieldMatrix:$input, UI64:$selector);
}
def Data_DomainMatrixColumnOp : DomainConstructor<"domain_matrix_column"> {
  let arguments = (ins FieldMatrix:$input, UI64:$selector);
}
def Data_DomainMatrixCoordinatesOp : DomainConstructor<"domain_matrix_coordinates"> {
  let arguments = (ins FieldMatrix:$input, StrAttr:$order);
}
def Data_DomainYieldOp : Op<DataDialect, "domain_yield",
    [Terminator, HasParent<"::zkc::data::DomainOp">]> {
  let arguments = (ins Domain:$input);
}
def Data_BoundedAtOp : Op<DataDialect, "bounded_at", [Pure, DeclareOpInterfaceMethods<MathematicalOpInterface>]> {
  let arguments = (ins AnyType:$input, UI64:$index);
  let results = (outs AnyType:$output);
  let hasVerifier = 1;
}
def Data_BoundedMatrixAtOp : Op<DataDialect, "bounded_matrix_at", [Pure, DeclareOpInterfaceMethods<MathematicalOpInterface>]> {
  let arguments = (ins FieldMatrix:$input, UI64:$row, UI64:$column);
  let results = (outs AnyType:$output);
  let hasVerifier = 1;
}
def EncodingIndexUleb128ExecOp : BoundOp<DataDialect, "exec.encoding_index_uleb128", [OpEncodingIndexUleb128]>;
def BytesRepeatExecOp : BoundOp<DataDialect, "exec.bytes_repeat", [OpBytesRepeat]>;
def BytesJoinExecOp : BoundOp<DataDialect, "exec.bytes_join", [OpBytesJoin]>;
def BytesEmptyExecOp : BoundOp<DataDialect, "exec.bytes_empty", [OpBytesEmpty]>;
def BytesAppendExecOp : BoundOp<DataDialect, "exec.bytes_append", [OpBytesAppend]>;
def BytesConcatExecOp : BoundOp<DataDialect, "exec.bytes_concat", [OpBytesConcat]>;
def BytesSliceExecOp : BoundOp<DataDialect, "exec.bytes_slice", [OpBytesSlice]>;
def BytesAtExecOp : BoundOp<DataDialect, "exec.bytes_at", [OpBytesAt]>;
def BytesLengthExecOp : BoundOp<DataDialect, "exec.bytes_length", [OpBytesLength]>;
def BytesEqualExecOp : BoundOp<DataDialect, "exec.bytes_equal", [OpBytesEqual]>;
def SequenceEmptyExecOp : BoundOp<DataDialect, "exec.sequence_empty", [OpSequenceEmpty]>;
def SequenceAppendExecOp : BoundOp<DataDialect, "exec.sequence_append", [OpSequenceAppend]>;
def SequenceLengthExecOp : BoundOp<DataDialect, "exec.sequence_length", [OpSequenceLength]>;
def SequenceAtExecOp : BoundOp<DataDialect, "exec.sequence_at", [OpSequenceAt]>;
class DataExpression<string name, list<Trait> traits = []>
    : Op<DataDialect, name, !listconcat([Pure], traits)> {
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
def Data_IndexOp : DataExpression<"index", [DeclareOpInterfaceMethods<MathematicalOpInterface>]> {
  let arguments = (ins StrAttr:$value);
  let results = (outs UI64:$output);
}
def Data_EqualOp : DataExpression<"index_equal", [DeclareOpInterfaceMethods<MathematicalOpInterface>]> {
  let arguments = (ins UI64:$lhs, UI64:$rhs);
  let results = (outs I1:$output);
}
def Data_LessOp : DataExpression<"index_less", [DeclareOpInterfaceMethods<MathematicalOpInterface>]> {
  let arguments = (ins UI64:$lhs, UI64:$rhs);
  let results = (outs I1:$output);
}
def Data_PowerOfTwoOp : DataExpression<"index_power_of_two", [DeclareOpInterfaceMethods<MathematicalOpInterface>]> {
  let arguments = (ins UI64:$value, UI64:$exponent);
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
def Data_DimOp : DataExpression<"dim", [DeclareOpInterfaceMethods<MathematicalOpInterface>]> {
  let arguments = (ins AnyTypeOf<[FieldVector, GroupVector, Indices, Bytes,
                                 FieldMatrix, FieldArray]>:$input,
                       I64Attr:$axis);
  let results = (outs UI64:$output);
}
#endif
