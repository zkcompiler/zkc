#ifndef ZKC_DIALECT_DATA_IR_DATAOPS_TD
#define ZKC_DIALECT_DATA_IR_DATAOPS_TD
include "zkc/Dialect/Data/IR/DataDialect.td"
include "zkc/Dialect/Types.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
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
// Reads have no memory effects, but their totality depends on contextual bound
// evidence. Generic speculation cannot move them outside that evidence's scope.
def Data_BoundedAtOp : Op<DataDialect, "bounded_at", [NoMemoryEffect, DeclareOpInterfaceMethods<MathematicalOpInterface>]> {
  let arguments = (ins AnyType:$input, UI64:$index);
  let results = (outs AnyType:$output);
  let hasVerifier = 1;
}
def Data_BoundedMatrixAtOp : Op<DataDialect, "bounded_matrix_at", [NoMemoryEffect, DeclareOpInterfaceMethods<MathematicalOpInterface>]> {
  let arguments = (ins FieldMatrix:$input, UI64:$row, UI64:$column);
  let results = (outs AnyType:$output);
  let hasVerifier = 1;
}

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
def Data_IndexOp : DataExpression<"index", [ConstantLike,
    DeclareOpInterfaceMethods<MathematicalOpInterface>]> {
  let arguments = (ins UI64Attr:$value);
  let results = (outs UI64:$output);
  let hasVerifier = 0;
  let hasFolder = 1;
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
// Total unsigned-word mathematics on the existing index carrier. These have
// no overflow flags, parameters or domain-membership premises.
class DataIndexBinary<string name> : DataExpression<name,
    [DeclareOpInterfaceMethods<MathematicalOpInterface>]> {
  let arguments = (ins UI64:$lhs, UI64:$rhs);
  let results = (outs UI64:$output);
  let hasVerifier = 0;
}
def Data_IndexWrappingAddOp : DataIndexBinary<"index_wrapping_add"> {
  let summary = "Unsigned index addition modulo 2^64";
  let description = [{
    For all unsigned 64-bit operands a and b, return (a + b) modulo 2^64.
    This total mathematical operation does not change checked index.add.
  }];
}
def Data_IndexWrappingSubtractOp : DataIndexBinary<"index_wrapping_subtract"> {
  let summary = "Unsigned index subtraction modulo 2^64";
  let description = [{
    For all unsigned 64-bit operands a and b, return (a - b) modulo 2^64,
    represented in [0, 2^64). This does not change checked index.sub.
  }];
}
def Data_IndexBitAndOp : DataIndexBinary<"index_bit_and"> {
  let summary = "Bitwise conjunction of unsigned indices";
  let description = [{
    Result bit j is one exactly when bit j of both operands is one, for
    every j in [0, 64). All input pairs have a defined unsigned result.
  }];
}
// Counts at least 64 return zero; they are never reduced modulo 64.
def Data_IndexLogicalShiftRightOp : DataIndexBinary<"index_logical_shift_right"> {
  let summary = "Total unsigned logical right shift";
  let description = [{
    For value a and unsigned count b, return floor(a / 2^b) when b < 64,
    and zero when b >= 64. The count is not reduced modulo 64. No input
    introduces overflow, poison or an arithmetic refusal.
  }];
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
// Logical construction retains typed source layout. Formation checks shape;
// source admission separately establishes construction and projection rights.
def Data_ConstructOp : Op<DataDialect, "construct"> {
  let arguments = (ins Variadic<AnyType>:$inputs, StrAttr:$alternative);
  let results = (outs DataValue:$output);
  let hasVerifier = 1;
}
def Data_UnpackOp : Op<DataDialect, "unpack"> {
  let arguments = (ins DataValue:$input);
  let results = (outs Variadic<AnyType>:$outputs);
  let hasVerifier = 1;
}
def Data_ProjectOp : Op<DataDialect, "project"> {
  let arguments = (ins AnyType:$input, DenseI64ArrayAttr:$path);
  let results = (outs AnyType:$output);
  let hasVerifier = 1;
}
include "mlir/Interfaces/ControlFlowInterfaces.td"
def Data_MatchOp : Op<DataDialect, "match", [Terminator,
    DeclareOpInterfaceMethods<BranchOpInterface>]> {
  let arguments = (ins DataValue:$input,
    VariadicOfVariadic<AnyType, "successor_operand_segments">:$forwarded,
    DenseI32ArrayAttr:$successor_operand_segments, StrArrayAttr:$alternatives);
  let successors = (successor VariadicSuccessor<AnySuccessor>:$arms);
  let hasVerifier = 1;
}
#endif
