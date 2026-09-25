include "mlir/IR/AttrTypeBase.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "zkc/Dialect/Base.td"
include "zkc/Dialect/Relation.td"
include "zkc/Interfaces/SourceOpInterface.td"
def PIRDialect : ZKCDialect {
  let name = "pir";
  let cppNamespace = "::zkc";
  let useDefaultTypePrinterParser = 1;
}
def AlgebraDialect : ZKCDialect {
  let name = "algebra";
  let cppNamespace = "::zkc";
  let useDefaultTypePrinterParser = 1;
}
def PolynomialDialect : ZKCDialect {
  let name = "poly";
  let cppNamespace = "::zkc";
  let useDefaultTypePrinterParser = 1;
}
def PlanDialect : ZKCDialect {
  let name = "plan";
  let cppNamespace = "::zkc";
  let useDefaultTypePrinterParser = 1;
}
def Scalar : TypeDef<PlanDialect, "Scalar"> {
  let mnemonic = "scalar";
  let summary = "immediate scalar or immutable prepared scalar reference";
  let parameters = (ins StringRefParameter<"Resolved field">:$domain);
  let assemblyFormat = "`<` $domain `>`";
  let genVerifyDecl = 1;
}
def Flow : TypeDef<PIRDialect, "Flow"> {
  let mnemonic = "flow";
  let summary = "protocol ordering value";
}
def Digest : TypeDef<PIRDialect, "Digest"> {
  let mnemonic = "digest";
  let summary = "protocol digest";
}
def Summary : TypeDef<PIRDialect, "Summary"> {
  let mnemonic = "summary";
  let summary = "protocol summary";
}
def Field : TypeDef<AlgebraDialect, "Field"> {
  let mnemonic = "field";
  let summary = "resolved field element";
  let parameters = (ins StringRefParameter<"Resolved field">:$domain);
  let assemblyFormat = "`<` $domain `>`";
  let genVerifyDecl = 1;
}
class Shaped<string name, string spelling> : TypeDef<PolynomialDialect, name> {
  let mnemonic = spelling;
  let summary = "shaped polynomial value";
  let parameters = (ins StringRefParameter<"Resolved field">:$domain,
      StringRefParameter<"Original natural rank">:$rank);
  let assemblyFormat = "`<` $domain `,` $rank `>`";
  let genVerifyDecl = 1;
}
def Table : Shaped<"Table", "table">;
def Residual : Shaped<"Residual", "residual">;
def Point : TypeDef<PolynomialDialect, "Point"> {
  let mnemonic = "point";
  let summary = "polynomial point";
  let parameters = (ins StringRefParameter<"Resolved field">:$domain);
  let assemblyFormat = "`<` $domain `>`";
  let genVerifyDecl = 1;
}
class SourceOp<Dialect dialect, string name, list<Trait> traits>
    : Op<dialect, name,
         !listconcat(traits, [DeclareOpInterfaceMethods<SourceOpInterface>])> {
  let hasVerifier = 1;
}
def ViewOp : SourceOp<PolynomialDialect, "view", [Pure]> {
  let summary = "View in the resolved logical interpretation";
  let arguments = (ins Table:$origin);
  let results = (outs Residual:$value);
}
def RestrictOp
    : SourceOp<PolynomialDialect, "restrict", [MemoryEffects<[MemWrite]>]> {
  let summary = "Restrict in the resolved logical interpretation";
  let arguments = (ins Flow:$before, Residual:$view, Field:$point);
  let results = (outs Flow:$after, Residual:$value);
}
def EvaluateOp
    : SourceOp<PolynomialDialect, "evaluate", [MemoryEffects<[MemWrite]>]> {
  let summary = "Evaluate in the resolved logical interpretation";
  let arguments = (ins Flow:$before, Residual:$view, Point:$point);
  let results = (outs Flow:$after, Field:$value);
}
def AddOp : SourceOp<AlgebraDialect, "add", [Pure]> {
  let summary = "Add in the resolved logical interpretation";
  let arguments = (ins Field:$lhs, Field:$rhs);
  let results = (outs Field:$value);
}
def RecordOp : SourceOp<PIRDialect, "record", [MemoryEffects<[MemWrite]>]> {
  let summary = "Record in the resolved logical interpretation";
  let arguments = (ins Flow:$before, Field:$input);
  let results = (outs Flow:$after, I1:$value);
}
def AbortWriteOp
    : SourceOp<PIRDialect, "abort_write", [MemoryEffects<[MemWrite]>]> {
  let summary = "Abort write in the resolved logical interpretation";
  let arguments = (ins Flow:$before, Field:$input);
  let results = (outs Flow:$after, I1:$value);
}
def OrderedPairOp : SourceOp<PIRDialect, "ordered_pair", [Pure]> {
  let summary = "Ordered pair in the resolved logical interpretation";
  let arguments = (ins Digest:$lhs, Digest:$rhs);
  let results = (outs Digest:$value);
}
def PackOp : SourceOp<PIRDialect, "pack", [Pure]> {
  let summary = "Pack in the resolved logical interpretation";
  let arguments = (ins Field:$two, Field:$seven, Digest:$digest);
  let results = (outs Summary:$value);
}
def SendOp : SourceOp<PIRDialect, "send", [MemoryEffects<[MemWrite]>]> {
  let summary = "Send in the resolved logical interpretation";
  let arguments = (ins Flow:$before, Field:$atZero, Field:$atOne);
  let results = (outs Flow:$after, I1:$value);
}
def DrawOp : SourceOp<PIRDialect, "draw", [MemoryEffects<[MemWrite]>]> {
  let summary = "Draw in the resolved logical interpretation";
  let arguments = (ins Flow:$before);
  let results = (outs Flow:$after, Field:$value);
}
def LinearOp : SourceOp<PolynomialDialect, "linear", [Pure]> {
  let summary = "Linear in the resolved logical interpretation";
  let arguments = (ins Field:$atZero, Field:$atOne, Field:$point);
  let results = (outs Field:$value);
}
def PointOp : SourceOp<PolynomialDialect, "point", [Pure]> {
  let summary = "Point in the resolved logical interpretation";
  let arguments = (ins Field:$input);
  let results = (outs Point:$value);
}
def EndpointPointOp : SourceOp<PolynomialDialect, "endpoint_point", [Pure]> {
  let summary = "Endpoint point in the resolved logical interpretation";
  let arguments = (ins BoolAttr:$atOne);
  let results = (outs Point:$value);
}
def EqualOp : SourceOp<AlgebraDialect, "equal", [Pure]> {
  let summary = "Equal in the resolved logical interpretation";
  let arguments = (ins Field:$lhs, Field:$rhs);
  let results = (outs I1:$value);
}
def ParentOp : SourceOp<PIRDialect, "parent", [Pure]> {
  let summary = "Parent in the resolved logical interpretation";
  let arguments = (ins Digest:$input, Digest:$sibling, BoolAttr:$left);
  let results = (outs Digest:$value);
}
def DigestEqualOp : SourceOp<PIRDialect, "digest_equal", [Pure]> {
  let summary = "Digest equal in the resolved logical interpretation";
  let arguments = (ins Digest:$lhs, Digest:$rhs);
  let results = (outs I1:$value);
}
def PIRProgramOp : Op<PIRDialect, "program", [IsolatedFromAbove, SingleBlock]> {
  let summary = "Retain the participant algorithm and its binding context";
  let arguments = (ins StrAttr:$context, TypeAttr:$resultType,
      OptionalAttr<StrAttr>:$sourceFormat);
  let regions = (region AnyRegion:$body);
  let hasRegionVerifier = 1;
}
def PIRReturnOp : Op<PIRDialect, "return", [Terminator, ParentOneOf<["PIRProgramOp", "PlanProgramOp", "PIRChooseOp", "PlanChooseOp", "PIRRepeatOp", "PlanRepeatOp", "PIRBindOp", "PlanBindOp"]>]> {
  let arguments = (ins Flow:$flow, AnyType:$value);
}
def PIRStopOp : Op<PIRDialect, "stop", [Terminator, ParentOneOf<["PIRProgramOp", "PlanProgramOp", "PIRChooseOp", "PlanChooseOp", "PIRRepeatOp", "PlanRepeatOp", "PIRBindOp", "PlanBindOp"]>]> {
  let arguments = (ins Flow:$flow, StrAttr:$reason);
  let hasVerifier = 1;
}
def PIRChooseOp : Op<PIRDialect, "choose", [IsolatedFromAbove, Terminator, ParentOneOf<["PIRProgramOp", "PlanProgramOp", "PIRChooseOp", "PlanChooseOp", "PIRRepeatOp", "PlanRepeatOp", "PIRBindOp", "PlanBindOp"]>]> {
  let summary = "Run exactly one continuation, propagating every logical stop";
  let arguments = (ins Flow:$flow, AnyType:$condition,
      Variadic<AnyType>:$captures);
  let regions = (region AnyRegion:$yes, AnyRegion:$no);
}
def PIRRepeatOp : Op<PIRDialect, "repeat", [IsolatedFromAbove, ParentOneOf<["PIRProgramOp", "PlanProgramOp", "PIRChooseOp", "PlanChooseOp", "PIRRepeatOp", "PlanRepeatOp", "PIRBindOp", "PlanBindOp"]>]> {
  let summary =
      "Repeat a stopped accumulator computation a public natural count";
  let arguments = (ins Flow:$before, AnyType:$initial,
      Variadic<AnyType>:$captures, StrAttr:$count);
  let results = (outs Flow:$after, AnyType:$value);
  let regions = (region AnyRegion:$body);
}
def PIRBindOp : Op<PIRDialect, "bind", [IsolatedFromAbove, SingleBlock, ParentOneOf<["PIRProgramOp", "PlanProgramOp", "PIRChooseOp", "PlanChooseOp", "PIRRepeatOp", "PlanRepeatOp", "PIRBindOp", "PlanBindOp"]>]> {
  let summary = "Run a region and bind its returned value to one shared suffix";
  let arguments = (ins Flow:$before, Variadic<AnyType>:$captures);
  let results = (outs Flow:$after, AnyType:$value);
  let regions = (region AnyRegion:$body);
}
def PlanProgramOp
    : Op<PlanDialect, "program", [IsolatedFromAbove, SingleBlock]> {
  let summary = "Retain the participant algorithm and its binding context";
  let arguments = (ins StrAttr:$context, TypeAttr:$resultType,
      OptionalAttr<StrAttr>:$sourceFormat, OptionalAttr<StrAttr>:$realization);
  let regions = (region AnyRegion:$body);
  let hasRegionVerifier = 1;
}
def PlanReturnOp : Op<PlanDialect, "return", [Terminator, ParentOneOf<["PIRProgramOp", "PlanProgramOp", "PIRChooseOp", "PlanChooseOp", "PIRRepeatOp", "PlanRepeatOp", "PIRBindOp", "PlanBindOp"]>]> {
  let arguments = (ins Flow:$flow, AnyType:$value);
}
def PlanStopOp : Op<PlanDialect, "stop", [Terminator, ParentOneOf<["PIRProgramOp", "PlanProgramOp", "PIRChooseOp", "PlanChooseOp", "PIRRepeatOp", "PlanRepeatOp", "PIRBindOp", "PlanBindOp"]>]> {
  let arguments = (ins Flow:$flow, StrAttr:$reason);
  let hasVerifier = 1;
}
def PlanChooseOp : Op<PlanDialect, "choose", [IsolatedFromAbove, Terminator, ParentOneOf<["PIRProgramOp", "PlanProgramOp", "PIRChooseOp", "PlanChooseOp", "PIRRepeatOp", "PlanRepeatOp", "PIRBindOp", "PlanBindOp"]>]> {
  let summary = "Run exactly one continuation, propagating every logical stop";
  let arguments = (ins Flow:$flow, AnyType:$condition,
      Variadic<AnyType>:$captures);
  let regions = (region AnyRegion:$yes, AnyRegion:$no);
}
def PlanRepeatOp : Op<PlanDialect, "repeat", [IsolatedFromAbove, ParentOneOf<["PIRProgramOp", "PlanProgramOp", "PIRChooseOp", "PlanChooseOp", "PIRRepeatOp", "PlanRepeatOp", "PIRBindOp", "PlanBindOp"]>]> {
  let summary =
      "Repeat a stopped accumulator computation a public natural count";
  let arguments = (ins Flow:$before, AnyType:$initial,
      Variadic<AnyType>:$captures, StrAttr:$count);
  let results = (outs Flow:$after, AnyType:$value);
  let regions = (region AnyRegion:$body);
}
def PlanBindOp : Op<PlanDialect, "bind", [IsolatedFromAbove, SingleBlock, ParentOneOf<["PIRProgramOp", "PlanProgramOp", "PIRChooseOp", "PlanChooseOp", "PIRRepeatOp", "PlanRepeatOp", "PIRBindOp", "PlanBindOp"]>]> {
  let summary = "Run a region and bind its returned value to one shared suffix";
  let arguments = (ins Flow:$before, Variadic<AnyType>:$captures);
  let results = (outs Flow:$after, AnyType:$value);
  let regions = (region AnyRegion:$body);
}
def PrepareOp : Op<PlanDialect, "prepare", [MemoryEffects<[MemRead, MemWrite]>]> {
  let summary = "check a table query and retain a deferred or materialized scalar";
  let arguments = (ins Flow:$before, Residual:$view, Point:$point, StrAttr:$mode);
  let results = (outs Flow:$after, Scalar:$value);
  let hasVerifier = 1;
}
def InvokeOp : Op<PlanDialect, "invoke", [MemoryEffects<[MemRead, MemWrite]>]> {
  let summary = "consume physical operands under an installed operation contract";
  let arguments = (ins Variadic<AnyType>:$inputs, StrAttr:$descriptor);
  let results = (outs Variadic<AnyType>:$outputs);
  let hasVerifier = 1;
}

include "zkc/Dialect/Types.td"
include "zkc/Dialect/Protocol.td"
include "zkc/Dialect/Participant.td"
include "zkc/Dialect/Kernels.td"
include "zkc/Dialect/Physical.td"

include "zkc/Dialect/Claim.td"
