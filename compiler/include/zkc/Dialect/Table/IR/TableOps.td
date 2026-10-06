#ifndef ZKC_DIALECT_TABLE_IR_TABLEOPS_TD
#define ZKC_DIALECT_TABLE_IR_TABLEOPS_TD

include "zkc/Dialect/Types.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "zkc/Dialect/Kernels.td"
include "zkc/Interfaces/SourceOpInterface.td"

class SourceOp<Dialect dialect, string name, list<Trait> traits>
    : Op<dialect, name,
         !listconcat(traits, [DeclareOpInterfaceMethods<SourceOpInterface>])> {
  let hasVerifier = 1;
}

def AddOp : SourceOp<TableDialect, "field_add", [Pure]> {
  let summary = "Add in the resolved logical interpretation";
  let arguments = (ins Field:$lhs, Field:$rhs);
  let results = (outs Field:$value);
}

def EqualOp : SourceOp<TableDialect, "field_equal", [Pure]> {
  let summary = "Equal in the resolved logical interpretation";
  let arguments = (ins Field:$lhs, Field:$rhs);
  let results = (outs I1:$value);
}

def AbortWriteOp
    : SourceOp<TableDialect, "abort_write", [MemoryEffects<[MemWrite]>]> {
  let summary = "Abort write in the resolved logical interpretation";
  let arguments = (ins Flow:$before, Field:$input);
  let results = (outs Flow:$after, I1:$value);
}

def PIRBindOp : Op<TableDialect, "source.bind", [IsolatedFromAbove, SingleBlock, ParentOneOf<["zkc::table::PIRProgramOp", "zkc::table::PlanProgramOp", "zkc::table::PIRChooseOp", "zkc::table::PlanChooseOp", "zkc::table::PIRRepeatOp", "zkc::table::PlanRepeatOp", "zkc::table::PIRBindOp", "zkc::table::PlanBindOp"]>]> {
  let summary = "Run a region and bind its returned value to one shared suffix";
  let arguments = (ins Flow:$before, Variadic<AnyType>:$captures);
  let results = (outs Flow:$after, AnyType:$value);
  let regions = (region AnyRegion:$body);
}

def PIRChooseOp : Op<TableDialect, "source.choose", [IsolatedFromAbove, Terminator, ParentOneOf<["zkc::table::PIRProgramOp", "zkc::table::PlanProgramOp", "zkc::table::PIRChooseOp", "zkc::table::PlanChooseOp", "zkc::table::PIRRepeatOp", "zkc::table::PlanRepeatOp", "zkc::table::PIRBindOp", "zkc::table::PlanBindOp"]>]> {
  let summary = "Run exactly one continuation, propagating every logical stop";
  let arguments = (ins Flow:$flow, AnyType:$condition,
      Variadic<AnyType>:$captures);
  let regions = (region AnyRegion:$yes, AnyRegion:$no);
}

def DigestEqualOp : SourceOp<TableDialect, "digest_equal", [Pure]> {
  let summary = "Digest equal in the resolved logical interpretation";
  let arguments = (ins Digest:$lhs, Digest:$rhs);
  let results = (outs I1:$value);
}

def DrawOp : SourceOp<TableDialect, "draw", [MemoryEffects<[MemWrite]>]> {
  let summary = "Draw in the resolved logical interpretation";
  let arguments = (ins Flow:$before);
  let results = (outs Flow:$after, Field:$value);
}

def OrderedPairOp : SourceOp<TableDialect, "ordered_pair", [Pure]> {
  let summary = "Ordered pair in the resolved logical interpretation";
  let arguments = (ins Digest:$lhs, Digest:$rhs);
  let results = (outs Digest:$value);
}

def PackOp : SourceOp<TableDialect, "pack", [Pure]> {
  let summary = "Pack in the resolved logical interpretation";
  let arguments = (ins Field:$two, Field:$seven, Digest:$digest);
  let results = (outs Summary:$value);
}

def ParentOp : SourceOp<TableDialect, "parent", [Pure]> {
  let summary = "Parent in the resolved logical interpretation";
  let arguments = (ins Digest:$input, Digest:$sibling, BoolAttr:$left);
  let results = (outs Digest:$value);
}

def PIRProgramOp : Op<TableDialect, "source.program", [IsolatedFromAbove, SingleBlock]> {
  let summary = "Retain the participant algorithm and its binding context";
  let arguments = (ins StrAttr:$context, TypeAttr:$resultType,
      OptionalAttr<StrAttr>:$sourceFormat);
  let regions = (region AnyRegion:$body);
  let hasRegionVerifier = 1;
}

def RecordOp : SourceOp<TableDialect, "record", [MemoryEffects<[MemWrite]>]> {
  let summary = "Record in the resolved logical interpretation";
  let arguments = (ins Flow:$before, Field:$input);
  let results = (outs Flow:$after, I1:$value);
}

def PIRRepeatOp : Op<TableDialect, "source.repeat", [IsolatedFromAbove, ParentOneOf<["zkc::table::PIRProgramOp", "zkc::table::PlanProgramOp", "zkc::table::PIRChooseOp", "zkc::table::PlanChooseOp", "zkc::table::PIRRepeatOp", "zkc::table::PlanRepeatOp", "zkc::table::PIRBindOp", "zkc::table::PlanBindOp"]>]> {
  let summary =
      "Repeat a stopped accumulator computation a public natural count";
  let arguments = (ins Flow:$before, AnyType:$initial,
      Variadic<AnyType>:$captures, StrAttr:$count);
  let results = (outs Flow:$after, AnyType:$value);
  let regions = (region AnyRegion:$body);
}

def PIRReturnOp : Op<TableDialect, "source.return", [Terminator, ParentOneOf<["zkc::table::PIRProgramOp", "zkc::table::PlanProgramOp", "zkc::table::PIRChooseOp", "zkc::table::PlanChooseOp", "zkc::table::PIRRepeatOp", "zkc::table::PlanRepeatOp", "zkc::table::PIRBindOp", "zkc::table::PlanBindOp"]>]> {
  let arguments = (ins Flow:$flow, AnyType:$value);
}

def SendOp : SourceOp<TableDialect, "send", [MemoryEffects<[MemWrite]>]> {
  let summary = "Send in the resolved logical interpretation";
  let arguments = (ins Flow:$before, Field:$atZero, Field:$atOne);
  let results = (outs Flow:$after, I1:$value);
}

def PIRStopOp : Op<TableDialect, "source.stop", [Terminator, ParentOneOf<["zkc::table::PIRProgramOp", "zkc::table::PlanProgramOp", "zkc::table::PIRChooseOp", "zkc::table::PlanChooseOp", "zkc::table::PIRRepeatOp", "zkc::table::PlanRepeatOp", "zkc::table::PIRBindOp", "zkc::table::PlanBindOp"]>]> {
  let arguments = (ins Flow:$flow, StrAttr:$reason);
  let hasVerifier = 1;
}

def PlanBindOp : Op<TableDialect, "plan.bind", [IsolatedFromAbove, SingleBlock, ParentOneOf<["zkc::table::PIRProgramOp", "zkc::table::PlanProgramOp", "zkc::table::PIRChooseOp", "zkc::table::PlanChooseOp", "zkc::table::PIRRepeatOp", "zkc::table::PlanRepeatOp", "zkc::table::PIRBindOp", "zkc::table::PlanBindOp"]>]> {
  let summary = "Run a region and bind its returned value to one shared suffix";
  let arguments = (ins Flow:$before, Variadic<AnyType>:$captures);
  let results = (outs Flow:$after, AnyType:$value);
  let regions = (region AnyRegion:$body);
}

def PlanChooseOp : Op<TableDialect, "plan.choose", [IsolatedFromAbove, Terminator, ParentOneOf<["zkc::table::PIRProgramOp", "zkc::table::PlanProgramOp", "zkc::table::PIRChooseOp", "zkc::table::PlanChooseOp", "zkc::table::PIRRepeatOp", "zkc::table::PlanRepeatOp", "zkc::table::PIRBindOp", "zkc::table::PlanBindOp"]>]> {
  let summary = "Run exactly one continuation, propagating every logical stop";
  let arguments = (ins Flow:$flow, AnyType:$condition,
      Variadic<AnyType>:$captures);
  let regions = (region AnyRegion:$yes, AnyRegion:$no);
}

def InvokeOp : Op<TableDialect, "plan.invoke", [MemoryEffects<[MemRead, MemWrite]>]> {
  let summary = "consume physical operands under an installed operation contract";
  let arguments = (ins Variadic<AnyType>:$inputs, StrAttr:$descriptor);
  let results = (outs Variadic<AnyType>:$outputs);
  let hasVerifier = 1;
}

def PrepareOp : Op<TableDialect, "plan.prepare", [MemoryEffects<[MemRead, MemWrite]>]> {
  let summary = "check a table query and retain a deferred or materialized scalar";
  let arguments = (ins Flow:$before, Residual:$view, Point:$point, StrAttr:$mode);
  let results = (outs Flow:$after, Scalar:$value);
  let hasVerifier = 1;
}

def PlanProgramOp
    : Op<TableDialect, "plan.program", [IsolatedFromAbove, SingleBlock]> {
  let summary = "Retain the participant algorithm and its binding context";
  let arguments = (ins StrAttr:$context, TypeAttr:$resultType,
      OptionalAttr<StrAttr>:$sourceFormat, OptionalAttr<StrAttr>:$realization);
  let regions = (region AnyRegion:$body);
  let hasRegionVerifier = 1;
}

def PlanRepeatOp : Op<TableDialect, "plan.repeat", [IsolatedFromAbove, ParentOneOf<["zkc::table::PIRProgramOp", "zkc::table::PlanProgramOp", "zkc::table::PIRChooseOp", "zkc::table::PlanChooseOp", "zkc::table::PIRRepeatOp", "zkc::table::PlanRepeatOp", "zkc::table::PIRBindOp", "zkc::table::PlanBindOp"]>]> {
  let summary =
      "Repeat a stopped accumulator computation a public natural count";
  let arguments = (ins Flow:$before, AnyType:$initial,
      Variadic<AnyType>:$captures, StrAttr:$count);
  let results = (outs Flow:$after, AnyType:$value);
  let regions = (region AnyRegion:$body);
}

def PlanReturnOp : Op<TableDialect, "plan.return", [Terminator, ParentOneOf<["zkc::table::PIRProgramOp", "zkc::table::PlanProgramOp", "zkc::table::PIRChooseOp", "zkc::table::PlanChooseOp", "zkc::table::PIRRepeatOp", "zkc::table::PlanRepeatOp", "zkc::table::PIRBindOp", "zkc::table::PlanBindOp"]>]> {
  let arguments = (ins Flow:$flow, AnyType:$value);
}

def PlanStopOp : Op<TableDialect, "plan.stop", [Terminator, ParentOneOf<["zkc::table::PIRProgramOp", "zkc::table::PlanProgramOp", "zkc::table::PIRChooseOp", "zkc::table::PlanChooseOp", "zkc::table::PIRRepeatOp", "zkc::table::PlanRepeatOp", "zkc::table::PIRBindOp", "zkc::table::PlanBindOp"]>]> {
  let arguments = (ins Flow:$flow, StrAttr:$reason);
  let hasVerifier = 1;
}

def EndpointPointOp : SourceOp<TableDialect, "poly_endpoint_point", [Pure]> {
  let summary = "Endpoint point in the resolved logical interpretation";
  let arguments = (ins BoolAttr:$atOne);
  let results = (outs Point:$value);
}

def EvaluateOp
    : SourceOp<TableDialect, "poly_evaluate", [MemoryEffects<[MemWrite]>]> {
  let summary = "Evaluate in the resolved logical interpretation";
  let arguments = (ins Flow:$before, Residual:$view, Point:$point);
  let results = (outs Flow:$after, Field:$value);
}

def LinearOp : SourceOp<TableDialect, "poly_linear", [Pure]> {
  let summary = "Linear in the resolved logical interpretation";
  let arguments = (ins Field:$atZero, Field:$atOne, Field:$point);
  let results = (outs Field:$value);
}

def PointOp : SourceOp<TableDialect, "poly_point", [Pure]> {
  let summary = "Point in the resolved logical interpretation";
  let arguments = (ins Field:$input);
  let results = (outs Point:$value);
}

def RestrictOp
    : SourceOp<TableDialect, "poly_restrict", [MemoryEffects<[MemWrite]>]> {
  let summary = "Restrict in the resolved logical interpretation";
  let arguments = (ins Flow:$before, Residual:$view, Field:$point);
  let results = (outs Flow:$after, Residual:$value);
}

def ViewOp : SourceOp<TableDialect, "poly_view", [Pure]> {
  let summary = "View in the resolved logical interpretation";
  let arguments = (ins Table:$origin);
  let results = (outs Residual:$value);
}

#endif
