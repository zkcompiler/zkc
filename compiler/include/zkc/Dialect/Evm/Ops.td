// Separate physical EVM contracts. Logical layouts remain owned by
// NativeLayouts.
#ifndef ZKC_DIALECT_EVM_OPS_TD
#define ZKC_DIALECT_EVM_OPS_TD
include "mlir/IR/OpBase.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
def Evm_Dialect : Dialect {
  let name = "evm";
  let cppNamespace = "::zkc::evm";
}
def I256 : I<256>;
def Evm_Lane : AnyTypeOf<[I1, I32, I64, I256]>;
def Evm_FieldLane : AnyTypeOf<[I64, I256]>;
def Evm_FieldLiteral
    : Attr<CPred<"::llvm::isa<::zkc::algebra::FieldLiteralAttr>($_self)">,
           "exact canonical field literal"> {
  let storageType = "::zkc::algebra::FieldLiteralAttr";
  let returnType = storageType;
  let convertFromStorage = "$_self";
}
def Evm_NativeOrigin
    : Attr<CPred<"::llvm::isa<::zkc::runtime::NativeOriginAttr>($_self)">,
           "shared source-relative native origin"> {
  let storageType = "::zkc::runtime::NativeOriginAttr";
  let returnType = storageType;
  let convertFromStorage = "$_self";
}
// Reverts, allocation, immutable reads and affine transitions are observable.
// Default-resource read/write effects preserve their relative order and prevent
// unused-result elimination; no checked operation is speculatable.
class Evm_OrderedOp<string name>
    : Op<Evm_Dialect, name, [MemoryEffects<[MemRead, MemWrite]>]>;
def Evm_GroupAddOp : Evm_OrderedOp<"group.add"> {
  let summary = "Checked BLS G1 addition on immutable padded affine points";
  let arguments = (ins I64:$lhs, I64:$rhs, TypeAttr:$value_type);
  let results = (outs I64:$result);
  let hasVerifier = 1;
}
def Evm_GroupScaleOp : Evm_OrderedOp<"group.scale"> {
  let summary = "Checked BLS G1 one-term MSM with a canonical Fr scalar";
  let arguments = (ins I64:$point, I256:$scalar, TypeAttr:$value_type);
  let results = (outs I64:$result);
  let hasVerifier = 1;
}
def Evm_GroupEqualOp : Evm_OrderedOp<"group.equal"> {
  let summary = "Equality of canonical immutable BLS G1 affine points";
  let arguments = (ins I64:$lhs, I64:$rhs, TypeAttr:$value_type);
  let results = (outs I1:$result);
  let hasVerifier = 1;
}
def Evm_IndexAddOp : Evm_OrderedOp<"index.add"> {
  let summary = "Ordered checked unsigned index add";
  let arguments = (ins I64:$lhs, I64:$rhs);
  let results = (outs I64:$result);
  let hasVerifier = 1;
}
def Evm_IndexSubOp : Evm_OrderedOp<"index.sub"> {
  let summary = "Ordered checked unsigned index sub";
  let arguments = (ins I64:$lhs, I64:$rhs);
  let results = (outs I64:$result);
  let hasVerifier = 1;
}
def Evm_IndexMulOp : Evm_OrderedOp<"index.mul"> {
  let summary = "Ordered checked unsigned index mul";
  let arguments = (ins I64:$lhs, I64:$rhs);
  let results = (outs I64:$result);
  let hasVerifier = 1;
}
def Evm_IndexDivOp : Evm_OrderedOp<"index.div"> {
  let summary = "Ordered checked unsigned index div";
  let arguments = (ins I64:$lhs, I64:$rhs);
  let results = (outs I64:$result);
  let hasVerifier = 1;
}
def Evm_IndexModOp : Evm_OrderedOp<"index.mod"> {
  let summary = "Ordered checked unsigned index mod";
  let arguments = (ins I64:$lhs, I64:$rhs);
  let results = (outs I64:$result);
  let hasVerifier = 1;
}
def Evm_IndexPowerOfTwoOp : Evm_OrderedOp<"index.power_of_two"> {
  let summary = "EVM index.power_of_two with exact physical lanes";
  let arguments = (ins I64:$value, I64:$exponent);
  let results = (outs I1:$result);
  let hasVerifier = 1;
}
def Evm_IndexLogicalShiftRightOp
    : Op<Evm_Dialect, "index.logical_shift_right", [Pure]> {
  let summary = "EVM index.logical_shift_right with exact physical lanes";
  let arguments = (ins I64:$value, I64:$amount);
  let results = (outs I64:$result);
  let hasVerifier = 1;
}
def Evm_FieldConstantOp : Evm_OrderedOp<"field.constant"> {
  let summary = "EVM field.constant with exact physical lanes";
  let arguments = (ins TypeAttr:$value_type, Evm_FieldLiteral:$value);
  let results = (outs Evm_FieldLane:$result);
  let hasVerifier = 1;
}
def Evm_FieldAddOp : Evm_OrderedOp<"field.add"> {
  let summary = "EVM field.add with exact physical lanes";
  let arguments = (ins Evm_FieldLane:$lhs, Evm_FieldLane:$rhs,
      TypeAttr:$value_type);
  let results = (outs Evm_FieldLane:$result);
  let hasVerifier = 1;
}
def Evm_FieldSubOp : Evm_OrderedOp<"field.sub"> {
  let summary = "EVM field.sub with exact physical lanes";
  let arguments = (ins Evm_FieldLane:$lhs, Evm_FieldLane:$rhs,
      TypeAttr:$value_type);
  let results = (outs Evm_FieldLane:$result);
  let hasVerifier = 1;
}
def Evm_FieldMulOp : Evm_OrderedOp<"field.mul"> {
  let summary = "EVM field.mul with exact physical lanes";
  let arguments = (ins Evm_FieldLane:$lhs, Evm_FieldLane:$rhs,
      TypeAttr:$value_type);
  let results = (outs Evm_FieldLane:$result);
  let hasVerifier = 1;
}
def Evm_FieldNegOp : Evm_OrderedOp<"field.neg"> {
  let summary = "EVM field.neg with exact physical lanes";
  let arguments = (ins Evm_FieldLane:$input, TypeAttr:$value_type);
  let results = (outs Evm_FieldLane:$result);
  let hasVerifier = 1;
}
def Evm_FieldEqualOp : Evm_OrderedOp<"field.equal"> {
  let summary = "EVM field.equal with exact physical lanes";
  let arguments = (ins Evm_FieldLane:$lhs, Evm_FieldLane:$rhs,
      TypeAttr:$value_type);
  let results = (outs I1:$result);
  let hasVerifier = 1;
}
def Evm_FieldFromIndexOp : Evm_OrderedOp<"field.from_index"> {
  let summary = "EVM field.from_index with exact physical lanes";
  let arguments = (ins I64:$input, TypeAttr:$value_type);
  let results = (outs Evm_FieldLane:$result);
  let hasVerifier = 1;
}
def Evm_FieldEmbedOp : Evm_OrderedOp<"field.embed"> {
  let summary = "EVM field.embed with exact physical lanes";
  let arguments = (ins I256:$input, TypeAttr:$value_type);
  let results = (outs Evm_FieldLane:$result);
  let hasVerifier = 1;
}
def Evm_FieldInverseOp : Evm_OrderedOp<"field.inverse"> {
  let summary = "EVM field.inverse with exact physical lanes";
  let arguments = (ins Evm_FieldLane:$input, TypeAttr:$value_type);
  let results = (outs Evm_FieldLane:$result);
  let hasVerifier = 1;
}
def Evm_VectorConstantOp : Evm_OrderedOp<"vector.constant"> {
  let summary = "EVM vector.constant with exact physical lanes";
  let arguments = (ins TypeAttr:$value_type, ArrayAttr:$values);
  let results = (outs I64:$result_data, I64:$result_count);
  let hasVerifier = 1;
}
def Evm_VectorEmptyOp : Evm_OrderedOp<"vector.empty"> {
  let summary = "EVM vector.empty with exact physical lanes";
  let arguments = (ins TypeAttr:$value_type);
  let results = (outs I64:$result_data, I64:$result_count);
  let hasVerifier = 1;
}
def Evm_VectorLengthOp : Evm_OrderedOp<"vector.length"> {
  let summary = "EVM vector.length with exact physical lanes";
  let arguments = (ins I64:$data, I64:$count, TypeAttr:$value_type);
  let results = (outs I64:$length);
  let hasVerifier = 1;
}
def Evm_VectorAppendOp : Evm_OrderedOp<"vector.append"> {
  let summary = "EVM vector.append with exact physical lanes";
  let arguments = (ins I64:$data, I64:$count, Evm_FieldLane:$element,
      TypeAttr:$value_type);
  let results = (outs I64:$result_data, I64:$result_count);
  let hasVerifier = 1;
}
def Evm_VectorSplitOp : Evm_OrderedOp<"vector.split"> {
  let summary = "EVM vector.split with exact physical lanes";
  let arguments = (ins I64:$data, I64:$count, TypeAttr:$value_type);
  let results = (outs I64:$left_data, I64:$left_count, I64:$right_data,
      I64:$right_count);
  let hasVerifier = 1;
}
def Evm_VectorSumOp : Evm_OrderedOp<"vector.sum"> {
  let summary = "EVM vector.sum with exact physical lanes";
  let arguments = (ins I64:$data, I64:$count, TypeAttr:$value_type);
  let results = (outs Evm_FieldLane:$result);
  let hasVerifier = 1;
}
def Evm_VectorAllocOp : Evm_OrderedOp<"vector.alloc"> {
  let summary = "EVM vector.alloc with exact physical lanes";
  let arguments = (ins I64:$capacity, TypeAttr:$value_type);
  let results = (outs I64:$buffer);
  let hasVerifier = 1;
}
def Evm_VectorGetOp : Evm_OrderedOp<"vector.get"> {
  let summary = "EVM vector.get with exact physical lanes";
  let arguments = (ins I64:$data, I64:$count, I64:$index, TypeAttr:$value_type);
  let results = (outs Evm_FieldLane:$result);
  let hasVerifier = 1;
}
def Evm_VectorSetOp : Evm_OrderedOp<"vector.set"> {
  let summary = "EVM vector.set with exact physical lanes";
  let arguments = (ins I64:$data, I64:$count, I64:$index,
      Evm_FieldLane:$element, TypeAttr:$value_type);
  let hasVerifier = 1;
}
def Evm_VectorEqualOp : Evm_OrderedOp<"vector.equal"> {
  let summary = "EVM vector.equal with exact physical lanes";
  let arguments = (ins I64:$data, I64:$count, I64:$rhs_data, I64:$rhs_count,
      TypeAttr:$value_type);
  let results = (outs I1:$result);
  let hasVerifier = 1;
}
def Evm_SequenceEmptyOp : Evm_OrderedOp<"sequence.empty"> {
  let summary = "EVM sequence.empty with exact physical lanes";
  let arguments = (ins TypeAttr:$value_type);
  let results = (outs I64:$result_data, I64:$result_count);
  let hasVerifier = 1;
}
def Evm_SequenceAppendOp : Evm_OrderedOp<"sequence.append"> {
  let summary = "EVM sequence.append with exact physical lanes";
  let arguments = (ins I64:$data, I64:$count, Variadic<Evm_Lane>:$element,
      TypeAttr:$value_type);
  let results = (outs I64:$result_data, I64:$result_count);
  let hasVerifier = 1;
}
def Evm_SequenceLengthOp : Evm_OrderedOp<"sequence.length"> {
  let summary = "EVM sequence.length with exact physical lanes";
  let arguments = (ins I64:$data, I64:$count, TypeAttr:$value_type);
  let results = (outs I64:$length);
  let hasVerifier = 1;
}
def Evm_SequenceGetOp : Evm_OrderedOp<"sequence.get"> {
  let summary = "EVM sequence.get with exact physical lanes";
  let arguments = (ins I64:$data, I64:$count, I64:$index, TypeAttr:$value_type);
  let results = (outs Variadic<Evm_Lane>:$element);
  let hasVerifier = 1;
}
def Evm_SequenceAllocOp : Evm_OrderedOp<"sequence.alloc"> {
  let summary = "EVM sequence.alloc with exact physical lanes";
  let arguments = (ins I64:$capacity, TypeAttr:$value_type);
  let results = (outs I64:$buffer);
  let hasVerifier = 1;
}
def Evm_SequenceSetOp : Evm_OrderedOp<"sequence.set"> {
  let summary = "EVM sequence.set with exact physical lanes";
  let arguments = (ins I64:$data, I64:$count, I64:$index,
      Variadic<Evm_Lane>:$element, TypeAttr:$value_type);
  let hasVerifier = 1;
}
def Evm_BytesEmptyOp : Evm_OrderedOp<"bytes.empty"> {
  let summary = "EVM bytes.empty with exact physical lanes";
  let arguments = (ins TypeAttr:$value_type);
  let results = (outs I64:$result_data, I64:$result_count);
  let hasVerifier = 1;
}
def Evm_BytesLengthOp : Evm_OrderedOp<"bytes.length"> {
  let summary = "EVM bytes.length with exact physical lanes";
  let arguments = (ins I64:$data, I64:$count, TypeAttr:$value_type);
  let results = (outs I64:$length);
  let hasVerifier = 1;
}
def Evm_BytesGetOp : Evm_OrderedOp<"bytes.get"> {
  let summary = "EVM bytes.get with exact physical lanes";
  let arguments = (ins I64:$data, I64:$count, I64:$index, TypeAttr:$value_type);
  let results = (outs I64:$result);
  let hasVerifier = 1;
}
def Evm_BytesAppendOp : Evm_OrderedOp<"bytes.append"> {
  let summary = "EVM bytes.append with exact physical lanes";
  let arguments = (ins I64:$data, I64:$count, I64:$element,
      TypeAttr:$value_type);
  let results = (outs I64:$result_data, I64:$result_count);
  let hasVerifier = 1;
}
def Evm_IndicesEmptyOp : Evm_OrderedOp<"indices.empty"> {
  let summary = "EVM indices.empty with exact physical lanes";
  let arguments = (ins TypeAttr:$value_type);
  let results = (outs I64:$result_data, I64:$result_count);
  let hasVerifier = 1;
}
def Evm_IndicesAppendOp : Evm_OrderedOp<"indices.append"> {
  let summary = "EVM indices.append with exact physical lanes";
  let arguments = (ins I64:$data, I64:$count, I64:$element,
      TypeAttr:$value_type);
  let results = (outs I64:$result_data, I64:$result_count);
  let hasVerifier = 1;
}
def Evm_VariantMakeOp : Evm_OrderedOp<"variant.make"> {
  let summary = "EVM variant.make with exact physical lanes";
  let arguments = (ins Variadic<Evm_Lane>:$payload, TypeAttr:$value_type,
      I32Attr:$alternative);
  let results = (outs I64:$data);
  let hasVerifier = 1;
}
def Evm_VariantTagOp : Evm_OrderedOp<"variant.tag"> {
  let summary = "EVM variant.tag with exact physical lanes";
  let arguments = (ins I64:$data, TypeAttr:$value_type);
  let results = (outs I64:$tag);
  let hasVerifier = 1;
}
def Evm_VariantGetOp : Evm_OrderedOp<"variant.get"> {
  let summary = "EVM variant.get with exact physical lanes";
  let arguments = (ins I64:$data, TypeAttr:$value_type, I32Attr:$alternative,
      I32Attr:$payload);
  let results = (outs Variadic<Evm_Lane>:$result);
  let hasVerifier = 1;
}
def Evm_ProofReceiveOp : Evm_OrderedOp<"proof.receive"> {
  let summary = "EVM proof.receive with exact physical lanes";
  let arguments = (ins TypeAttr:$value_type);
  let results = (outs Variadic<Evm_Lane>:$payload);
  let hasVerifier = 1;
}
def Evm_TranscriptObserveOp : Evm_OrderedOp<"transcript.observe"> {
  let summary = "EVM transcript.observe with exact physical lanes";
  let arguments = (ins I64:$scope, I64:$generation, Variadic<Evm_Lane>:$payload,
      I64:$coordinates, I64:$coordinate_count, TypeAttr:$value_type,
      Evm_NativeOrigin:$origin);
  let results = (outs I64:$next_generation);
  let hasVerifier = 1;
}
def Evm_TranscriptChallengeOp : Evm_OrderedOp<"transcript.challenge"> {
  let summary = "EVM transcript.challenge with exact physical lanes";
  let arguments = (ins I64:$scope, I64:$generation, I64:$coordinates,
      I64:$coordinate_count, TypeAttr:$value_type, Evm_NativeOrigin:$origin);
  let results = (outs Evm_FieldLane:$challenge, I64:$next_generation);
  let hasVerifier = 1;
}
def Evm_TranscriptIndexOp : Evm_OrderedOp<"transcript.index"> {
  let summary = "One checked power-of-two transcript index request";
  let arguments = (ins I64:$scope, I64:$generation, I64:$bound,
      I64:$coordinates, I64:$coordinate_count, StrAttr:$suite,
      Evm_NativeOrigin:$origin);
  let results = (outs I64:$index, I64:$next_generation);
  let hasVerifier = 1;
}
def Evm_TranscriptIndicesOp : Evm_OrderedOp<"transcript.indices"> {
  let summary = "One ordered native index block request";
  let arguments = (ins I64:$scope, I64:$generation,
      I64:$coordinates, I64:$coordinate_count, StrAttr:$suite,
      I64Attr:$bound, I64Attr:$count, Evm_NativeOrigin:$origin);
  let results = (outs I64:$indices, I64:$index_count, I64:$next_generation);
  let hasVerifier = 1;
}
def Evm_TranscriptIndicesGatedOp : Evm_OrderedOp<"transcript.indices_gated"> {
  let summary = "Check one native gated index block without searching";
  let arguments = (ins I64:$scope, I64:$generation, I64:$witness,
      I64:$coordinates, I64:$coordinate_count, StrAttr:$suite,
      I64Attr:$bound, I64Attr:$count, I64Attr:$difficulty,
      Evm_NativeOrigin:$origin);
  let results = (outs I64:$indices, I64:$index_count, I64:$next_generation);
  let hasVerifier = 1;
}
def Evm_ScopeCurrentOp : Evm_OrderedOp<"scope.current"> {
  let summary = "EVM scope.current with exact physical lanes";
  let results = (outs I64:$scope);
  let hasVerifier = 1;
}
def Evm_ScopeEnterOp : Evm_OrderedOp<"scope.enter"> {
  let summary = "EVM scope.enter with exact physical lanes";
  let arguments = (ins I64:$parent, I64:$generation);
  let results = (outs I64:$scope);
  let hasVerifier = 1;
}
def Evm_ScopeExitOp : Evm_OrderedOp<"scope.exit"> {
  let summary = "EVM scope.exit with exact physical lanes";
  let arguments = (ins I64:$scope, I64:$generation);
  let results = (outs I64:$ticket);
  let hasVerifier = 1;
}
def Evm_ScopeCheckOp : Evm_OrderedOp<"scope.check"> {
  let summary = "EVM scope.check with exact physical lanes";
  let arguments = (ins I64:$scope);
  let hasVerifier = 1;
}
def Evm_TransferMakeOp : Evm_OrderedOp<"transfer.make"> {
  let summary = "EVM transfer.make with exact physical lanes";
  let arguments = (ins I64:$scope);
  let results = (outs I64:$ticket);
  let hasVerifier = 1;
}
def Evm_TransferAcceptOp : Evm_OrderedOp<"transfer.accept"> {
  let summary = "EVM transfer.accept with exact physical lanes";
  let arguments = (ins I64:$scope, I64:$ticket);
  let hasVerifier = 1;
}
def Evm_TransferReleaseOp : Evm_OrderedOp<"transfer.release"> {
  let summary = "EVM transfer.release with exact physical lanes";
  let arguments = (ins I64:$ticket);
  let hasVerifier = 1;
}
def Evm_TransferCheckOp : Evm_OrderedOp<"transfer.check"> {
  let summary = "EVM transfer.check with exact physical lanes";
  let arguments = (ins I64:$ticket);
  let hasVerifier = 1;
}
def Evm_LoopBoundOp : Evm_OrderedOp<"loop.bound"> {
  let summary = "EVM loop.bound with exact physical lanes";
  let arguments = (ins I64:$count, I64:$maximum);
  let hasVerifier = 1;
}
def Evm_RangeCheckOp : Evm_OrderedOp<"range.check"> {
  let summary = "EVM range.check with exact physical lanes";
  let arguments = (ins I64:$lhs, I64:$rhs);
  let hasVerifier = 1;
}
def Evm_RangeAdmitOp : Evm_OrderedOp<"range.admit"> {
  let summary = "EVM range.admit with exact physical lanes";
  let arguments = (ins I64:$lower, I64:$upper);
  let hasVerifier = 1;
}
def Evm_SourceStopOp : Evm_OrderedOp<"source.stop"> {
  let summary = "EVM source.stop with exact physical lanes";
  let arguments = (ins OptionalAttr<StrAttr>:$site);
  let hasVerifier = 1;
}
def Evm_SourceGuardOp : Evm_OrderedOp<"source.guard"> {
  let summary = "EVM source.guard with exact physical lanes";
  let arguments = (ins I1:$condition, OptionalAttr<StrAttr>:$site);
  let hasVerifier = 1;
}
def Evm_RequireOp : Evm_OrderedOp<"control.require"> {
  let summary = "Preserve the bound backend require failure contract";
  let arguments = (ins I1:$condition);
  let hasVerifier = 1;
}
def Evm_OracleCheckOp : Evm_OrderedOp<"oracle.check"> {
  let summary = "Authenticate one complete row using an installed Keccak scheme";
  // Root and path lanes retain the existing complete native frame envelopes.
  let arguments = (ins I64:$root_data, I64:$root_bytes,
      I64:$width, I64:$height, I64:$position, I64:$row_data, I64:$row_count,
      I64:$path_data, I64:$path_bytes, TypeAttr:$value_type);
  let results = (outs I1:$result);
  let hasVerifier = 1;
}
def Evm_PolyDomainRootOp : Evm_OrderedOp<"poly.domain_root"> {
  let summary = "Exact installed base-subgroup root embedded in a field";
  let arguments = (ins I64:$size, TypeAttr:$value_type);
  let results = (outs Evm_FieldLane:$result);
  let hasVerifier = 1;
}
def Evm_PolyDomainPointOp : Evm_OrderedOp<"poly.domain_point"> {
  let summary = "Ordered checked coset coordinate with the installed root";
  let arguments = (ins Evm_FieldLane:$shift, I64:$size, I64:$position,
      TypeAttr:$value_type);
  let results = (outs Evm_FieldLane:$result);
  let hasVerifier = 1;
}
def Evm_PolyFromCoefficientsOp : Evm_OrderedOp<"poly.from_coefficients"> {
  let summary = "Allocate a normalized immutable ascending coefficient prefix";
  let arguments = (ins I64:$data, I64:$count, TypeAttr:$value_type);
  let results = (outs I64:$result_data, I64:$result_count);
  let hasVerifier = 1;
}
def Evm_PolyEvaluateOp : Evm_OrderedOp<"poly.univariate_evaluate"> {
  let summary = "Horner evaluation of an internal normalized polynomial";
  let arguments = (ins I64:$data, I64:$count, Evm_FieldLane:$point,
      TypeAttr:$value_type);
  let results = (outs Evm_FieldLane:$result);
  let hasVerifier = 1;
}
#endif
