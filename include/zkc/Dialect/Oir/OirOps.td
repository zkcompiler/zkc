//===- OirOps.td - Operator IR ops --------------------------*- tablegen
//-*-===//
// The oir operation vocabulary for the kernel carrier (docs/spec/
// endpoints.md, carrier.md). OIR is the image of a sealed protocol under
// the Fiat-Shamir handler: the first IR where optimization is legal
// again. Pure computation (constants, algebra) may be rewritten freely;
// protocol effects (transcript, proof stream, public binding, checks,
// decision) write the dialect's EndpointResource and are protected.
//
// Projection provenance is embedded, not sidecar'd: every operation that
// realizes a source obligation carries `src`, the canonical event positions
// (the encoder's numbering, kernel.md §8) of the sealed events it covers.
// Framing and pure construction operations need no source position. The
// ProjectionMap is a view derived by walking the program; coverage completeness
// is checked where both artifacts are in hand (pir-project, conformance
// tooling).
//===----------------------------------------------------------------------===//

#ifndef ZKC_DIALECT_OIR_OPS_TD
#define ZKC_DIALECT_OIR_OPS_TD

include "mlir/IR/Properties.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "zkc/Dialect/Oir/OirTypes.td"

def Oir_EndpointResource : Resource<"::zkc::oir::EndpointResource">;

defvar Oir_EndpointEffect = MemoryEffects<[MemWrite<Oir_EndpointResource>]>;

defvar Oir_SrcAttr = OptionalAttr<I64ArrayAttr>;

//===----------------------------------------------------------------------===//
// Containers. The artifact is the unit of identity: the program plus its
// embedded provenance plus the source citation. Route, ABI, and
// conformance facts are views (of the source artifact and the program
// signature), never materialized sections.
//===----------------------------------------------------------------------===//

def Oir_ArtifactOp
    : Oir_Op<"artifact", [NoTerminator, SingleBlock, NoRegionArguments,
                          IsolatedFromAbove]> {
  let summary = "one OIR artifact: endpoint program + provenance + citation";
  let description = [{
    The product of `pir-project` (docs/spec/boundaries.md §2): exactly
    one endpoint program, whose ops carry their source-event provenance,
    citing the sealed protocol by identity. `id` is the SHA-256 of the
    artifact's canonical encoding (program, provenance, citation);
    OIR defines no separate provenance-independent semantic digest.
  }];
  let arguments = (ins StringProp:$name, StringProp:$id, StringProp:$source,
      StringProp:$endpoint_kind);
  let regions = (region SizedRegion<1>:$body);
  let assemblyFormat = [{
    $name `id` $id `source` $source `endpoint` $endpoint_kind
    attr-dict-with-keyword $body
  }];
  let hasVerifier = 1;
}

def Oir_ProgramOp
    : Oir_Op<"program", [NoTerminator, SingleBlock, IsolatedFromAbove,
                         HasParent<"ArtifactOp">]> {
  let summary = "one OIR endpoint program";
  let description = [{
    The executable endpoint body. Entry block arguments are the public
    statement values (labelled by `statement_labels`, in order), then — on
    the prover endpoint only — one opaque witness-payload handle per
    `witness_labels` entry, then the proof stream. Pinned constructions are
    digest-gated through the `param_digests` artifact attribute before any
    transcript event; they are not caller-provided block arguments. Each
    channel has its own integrity discipline (docs/spec/endpoints.md §2). The
    transcript sponge is
    created inside; sponge, stream, and prover-side handles are linear
    by verification: every state is consumed exactly once, so
    reordering, skipping, or duplicating an absorption, a read, or a
    write is unrepresentable. `codecs` is the class-to-codec map baked
    in from kappa at projection: the artifact executes without the
    source (the profile is consumed at the boundary, not referenced
    through it). `witness_labels` is prover-endpoint ABI: an ordered
    list of [label, handle-class] pairs, present (possibly empty)
    exactly when the artifact's endpoint kind is `prover_skeleton`.
    `counterparty` records the obligations the counterparty realizes on
    successful `pir-project` output
    (docs/spec/endpoints.md §6.1): [position, discharge-kind]
    rows for the verifier-local checks a prover program deliberately
    does not emit, so COV_realized stays set equality in both
    directions; present exactly on prover programs. Standalone OIR verification
    does not yet reconstruct that coverage from the source artifact.
  }];
  let arguments = (ins DefaultValuedAttr<StrArrayAttr, "{}">:$statement_labels,
      DefaultValuedAttr<StrArrayAttr, "{}">:$param_digests,
      OptionalAttr<DictionaryAttr>:$codecs,
      OptionalAttr<ArrayAttr>:$witness_labels,
      OptionalAttr<ArrayAttr>:$counterparty);
  let regions = (region SizedRegion<1>:$body);
  let assemblyFormat = "attr-dict-with-keyword $body";
  let hasVerifier = 1;
}

//===----------------------------------------------------------------------===//
// The Fiat-Shamir family. Sponge threading is the operational half of
// the Binding Lemma (kernel.md §9.2): a challenge is a function of
// exactly the states absorbed before it.
//===----------------------------------------------------------------------===//

def Oir_TranscriptInitOp
    : Oir_Op<"transcript_init", [Oir_EndpointEffect, HasParent<"ProgramOp">]> {
  let summary = "initialize the transcript sponge";
  let description = [{
    `sponge` names the duplex construction (kappa vocabulary); `iv` is
    the initial-state policy — the artifact-id IV commits the transcript
    to the sealed protocol it executes.
  }];
  let arguments = (ins StringProp:$sponge, StringProp:$iv, Oir_SrcAttr:$src);
  let results = (outs Oir_SpongeType:$out);
  let assemblyFormat = "`sponge` $sponge `iv` $iv (`src` $src^)? attr-dict";
}

def Oir_AbsorbOp
    : Oir_Op<"absorb", [Oir_EndpointEffect, HasParent<"ProgramOp">]> {
  let summary = "absorb one value into the transcript";
  let arguments = (ins Oir_SpongeType:$sponge, Oir_ValType:$value,
      Oir_SrcAttr:$src);
  let results = (outs Oir_SpongeType:$out);
  let assemblyFormat = [{
    $sponge `,` $value `:` type($value) (`src` $src^)? attr-dict
  }];
}

def Oir_SqueezeOp : Oir_Op<"squeeze", [Oir_EndpointEffect, InferTypeOpAdaptor,
                                       HasParent<"ProgramOp">]> {
  let summary = "sample a counted scalar or vector challenge from the sponge";
  let description = [{
    The domain string separates challenge derivations — it enters the
    hash input, so two squeezes differing only in domain produce
    independent values (the operational half of kernel.md §1.5's D
    axis). The sampling rule and the space (the exact cardinality |C|
    as a minimal decimal string) are attributes: bounded and loop-free
    by design (unbounded rejection sampling would break both export
    forms and extraction). `payload_class` is the semantic class of each
    sample and selects its codec from the program map.  `count` is always
    explicit: `1` is scalar, a canonical decimal from 2 through 2^20 is a
    vector.  The
    whole sample is one persistent SSA handle of that semantic class; the
    result origin is `sampled` by inference.
  }];
  let arguments = (ins Oir_SpongeType:$sponge, StringProp:$label,
      StringProp:$payload_class, StringProp:$count, StringProp:$domain,
      StringProp:$rule, StringProp:$space, Oir_SrcAttr:$src);
  let results = (outs Oir_SpongeType:$out, Oir_ValType:$val);
  let assemblyFormat = [{
    $sponge $label `:` $payload_class `count` $count
    `domain` $domain `rule` $rule `space` $space
    (`src` $src^)? attr-dict
  }];
  let hasVerifier = 1;
}

//===----------------------------------------------------------------------===//
// The proof-stream family. Reads are canonical-or-reject; the final
// cursor must be consumed by expect_end — trailing bytes change the
// accept set.
//===----------------------------------------------------------------------===//

def Oir_ReadOp : Oir_Op<"read", [Oir_EndpointEffect, InferTypeOpAdaptor,
                                 HasParent<"ProgramOp">]> {
  let summary = "decode one counted value from the proof stream";
  let description = [{
    `count` mirrors the squeeze op's multiplicity: `1` is a scalar and
    a canonical decimal from 2 through 2^20 is a vector of that many
    values of the payload class, decoded in order at the class's fixed
    width — the wire carries no length framing, so the schedule is the
    only width authority (docs/spec/carrier.md §7). The whole vector is
    one SSA handle, exactly as a vector squeeze's.
  }];
  let arguments = (ins Oir_StreamType:$stream, StringProp:$label,
      StringProp:$payload_class,
      DefaultValuedProp<StringProp, "\"1\"">:$count, Oir_SrcAttr:$src);
  let results = (outs Oir_StreamType:$out, Oir_ValType:$val);
  let assemblyFormat = [{
    $stream $label `:` $payload_class (`count` $count^)?
    (`src` $src^)? attr-dict
  }];
  let hasVerifier = 1;
}

def Oir_ExpectEndOp
    : Oir_Op<"expect_end", [Oir_EndpointEffect, HasParent<"ProgramOp">]> {
  let summary = "require the proof stream exhausted";
  let arguments = (ins Oir_StreamType:$stream, Oir_SrcAttr:$src);
  let assemblyFormat = "$stream (`src` $src^)? attr-dict";
}

//===----------------------------------------------------------------------===//
// Pure computation: the region where rewriting is legal again. Constants
// and algebra realize transparent check interiors; they carry provenance
// but no effects.
//===----------------------------------------------------------------------===//

def Oir_ConstantOp
    : Oir_Op<"constant", [Pure, InferTypeOpAdaptor, HasParent<"ProgramOp">]> {
  let summary = "pinned protocol constant";
  let arguments = (ins StringProp:$value, StringProp:$payload_class,
      Oir_SrcAttr:$src);
  let results = (outs Oir_ValType:$val);
  let assemblyFormat = "$value `:` $payload_class (`src` $src^)? attr-dict";
}

// Result type inference for the algebra: the result class derives
// from the first operand and the origin is `derived` — origins are
// decided by the producing op, so the three channels' integrity
// disciplines stay type-level facts. Defined once here; every algebra
// op instantiates it.
class Oir_BinaryAlgebraOp<string mnemonic>
    : Oir_Op<mnemonic, [Pure, InferTypeOpAdaptor, HasParent<"ProgramOp">]> {
  let arguments = (ins Oir_ValType:$lhs, Oir_ValType:$rhs, Oir_SrcAttr:$src);
  let results = (outs Oir_ValType:$val);
  let assemblyFormat = [{
    $lhs `,` $rhs `:` type($lhs) `,` type($rhs) (`src` $src^)? attr-dict
  }];
  let extraClassDefinition = [{
    ::llvm::LogicalResult $cppClass::inferReturnTypes(
        ::mlir::MLIRContext *ctx, ::std::optional<::mlir::Location>,
        Adaptor adaptor,
        ::llvm::SmallVectorImpl<::mlir::Type> &inferredReturnTypes) {
      auto lhs = ::mlir::cast<ValType>(adaptor.getLhs().getType());
      inferredReturnTypes.push_back(
          ValType::get(ctx, lhs.getValueClass(), "derived"));
      return ::mlir::success();
    }
  }];
}

def Oir_GExpOp : Oir_BinaryAlgebraOp<"g_exp"> {
  let summary = "group exponentiation";
}
def Oir_GMulOp : Oir_BinaryAlgebraOp<"g_mul"> {
  let summary = "group multiplication";
}
def Oir_FAddOp : Oir_BinaryAlgebraOp<"f_add"> {
  let summary = "field addition";
}
def Oir_FMulOp : Oir_BinaryAlgebraOp<"f_mul"> {
  let summary = "field multiplication";
}

def Oir_FNegOp
    : Oir_Op<"f_neg", [Pure, InferTypeOpAdaptor, HasParent<"ProgramOp">]> {
  let summary = "field negation";
  let arguments = (ins Oir_ValType:$operand, Oir_SrcAttr:$src);
  let results = (outs Oir_ValType:$val);
  let assemblyFormat = "$operand `:` type($operand) (`src` $src^)? attr-dict";
  let extraClassDefinition = [{
    ::llvm::LogicalResult $cppClass::inferReturnTypes(
        ::mlir::MLIRContext *ctx, ::std::optional<::mlir::Location>,
        Adaptor adaptor,
        ::llvm::SmallVectorImpl<::mlir::Type> &inferredReturnTypes) {
      auto operand = ::mlir::cast<ValType>(adaptor.getOperand().getType());
      inferredReturnTypes.push_back(
          ValType::get(ctx, operand.getValueClass(), "derived"));
      return ::mlir::success();
    }
  }];
}

//===----------------------------------------------------------------------===//
// Decision sinks. Non-pure: a dropped assert is a soundness bug, so
// every sink writes the endpoint resource.
//===----------------------------------------------------------------------===//

def Oir_AssertEqOp
    : Oir_Op<"assert_eq", [Oir_EndpointEffect, HasParent<"ProgramOp">]> {
  let summary = "equality check: reject on mismatch";
  let arguments = (ins Oir_ValType:$lhs, Oir_ValType:$rhs, StringProp:$label,
      Oir_SrcAttr:$src);
  let assemblyFormat = [{
    $lhs `,` $rhs `:` type($lhs) `,` type($rhs) `as` $label
    (`src` $src^)? attr-dict
  }];
}

def Oir_CheckCallOp
    : Oir_Op<"check_call", [Oir_EndpointEffect, HasParent<"ProgramOp">]> {
  let summary = "opaque registered check";
  let description = [{
    A registry-backed component with no hidden protocol effects
    (docs/spec/endpoints.md §1): it may not read the stream, query the sponge,
    bind publics, or change routes — such effects must be OIR events of
    their own. `kind` is a human-readable contract id; `contract_digest` is
    the dispatch authority copied from the sealed vocabulary. Endpoint
    execution may not reinterpret the id under different registry content.
  }];
  let arguments = (ins Variadic<Oir_ValType>:$inputs, StringProp:$label,
      StringProp:$kind, StringProp:$contract_digest,
      DefaultValuedAttr<StrArrayAttr, "{}">:$params, Oir_SrcAttr:$src);
  let assemblyFormat = [{
    $label `kind` $kind `digest` $contract_digest
    (`(` $inputs^ `:` type($inputs) `)`)?
    (`params` $params^)? (`src` $src^)? attr-dict
  }];
  let hasVerifier = 1;
}

def Oir_DecideOp
    : Oir_Op<"decide", [Oir_EndpointEffect, HasParent<"ProgramOp">]> {
  let summary = "the endpoint decision: accept if every check held";
  let description = [{
    Consumes the final sponge state — the decision is a function of the
    whole transcript, and consuming it closes the sponge chain the way
    expect_end closes the stream: both linear resources are fully
    threaded from creation to a mandatory terminal consumer.
  }];
  let arguments = (ins Oir_SpongeType:$sponge, Oir_SrcAttr:$src);
  let assemblyFormat = "$sponge (`src` $src^)? attr-dict";
}

//===----------------------------------------------------------------------===//
// The prover endpoint family (docs/spec/endpoints.md §6). The
// write cursor is the read cursor's dual; holes are digest-authorized
// opaque compute with no protocol effects; end_stream and finish are
// the prover frame's terminal consumers. Admission is per endpoint
// kind: these ops are invalid inside a verifier program, and the
// verifier's decision sinks are invalid inside a prover program.
//===----------------------------------------------------------------------===//

def Oir_WriteOp
    : Oir_Op<"write", [Oir_EndpointEffect, HasParent<"ProgramOp">]> {
  let summary = "encode one value onto the proof stream";
  let description = [{
    The dual of `oir.read`: encodes the value through its payload
    class's codec (the codec's encode direction — round-tripping and
    canonical by obligation, so emitted proofs are canonical by
    construction) and appends it to the wire. The operand's origin may
    be `hole`, `derived`, `public`, or `pinned` — never `sampled`: a
    challenge is never a write operand directly; challenge-derived wire
    content flows through a declared hole or derived binding, keeping
    the dependence explicit in the route table.
  }];
  let arguments = (ins Oir_StreamType:$stream, Oir_ValType:$value,
      StringProp:$label, StringProp:$payload_class,
      DefaultValuedProp<StringProp, "\"1\"">:$count, Oir_SrcAttr:$src);
  let results = (outs Oir_StreamType:$out);
  let assemblyFormat = [{
    $stream `,` $value `:` type($value) `as` $label `class` $payload_class
    (`count` $count^)? (`src` $src^)? attr-dict
  }];
  let hasVerifier = 1;
}

def Oir_HoleCallOp : Oir_Op<"hole_call", [HasParent<"ProgramOp">]> {
  let summary = "digest-authorized opaque prover compute hole";
  let description = [{
    A registry-backed compute contract with no protocol effects: it may
    not absorb, squeeze, read or write the wire, bind publics, or
    verify artifacts — its outputs reach the transcript and the wire
    only through the spine's own events. Holes schedule freely subject
    to SSA dependence and handle linearity, and deliberately carry no
    `src`: a hole covers no obligation. `kind` classifies the primary
    output (commit | extend | evaluate | fold | open | pow_search) for
    diagnostics and coverage bucketing; the typed signature is the
    authority, and `contract_digest` — copied from the sealed
    vocabulary — is the sole dispatch authority. Only a `pow_search`
    hole may take the sponge, read-only: one sponge operand, one
    sponge result, state-identical by semantic requirement (a peek).
    Value results have origin `hole`.

    `params` and `semantic_params` are the cited contract's static and
    semantic parameter bindings, each in that contract's own name order —
    the contract fixes the order, so the values travel positionally and
    a source-free consumer recovers the names by re-resolving the digest.
    A semantic parameter is a content reference: the identity of material
    (a reference string, a verifier key) the supplier must hold matching
    content for. Carrying it here is what lets an endpoint be admitted and
    executed without its protocol.
  }];
  let arguments =
      (ins Variadic<
           AnyTypeOf<[Oir_ValType, Oir_HandleType, Oir_SpongeType]>>:$inputs,
          StringProp:$label, StringProp:$kind, StringProp:$contract_digest,
          DefaultValuedAttr<StrArrayAttr, "{}">:$params,
          DefaultValuedAttr<StrArrayAttr, "{}">:$semantic_params,
          DefaultValuedAttr<StrArrayAttr, "{}">:$result_counts);
  let results = (outs Variadic<
      AnyTypeOf<[Oir_ValType, Oir_HandleType, Oir_SpongeType]>>:$outputs);
  let assemblyFormat = [{
    $label `kind` $kind `digest` $contract_digest
    (`(` $inputs^ `:` type($inputs) `)`)?
    (`->` type($outputs)^)?
    (`params` $params^)?
    (`semantic` $semantic_params^)?
    (`result_counts` $result_counts^)? attr-dict
  }];
  let hasVerifier = 1;
}

def Oir_EndStreamOp
    : Oir_Op<"end_stream", [Oir_EndpointEffect, HasParent<"ProgramOp">]> {
  let summary = "the wire is complete";
  let description = [{
    The dual of `oir.expect_end`: consumes the final write cursor,
    declaring every routed slot written, in spine order. The program's
    output is the wire accumulated here.
  }];
  let arguments = (ins Oir_StreamType:$stream, Oir_SrcAttr:$src);
  let assemblyFormat = "$stream (`src` $src^)? attr-dict";
}

def Oir_FinishOp
    : Oir_Op<"finish", [Oir_EndpointEffect, HasParent<"ProgramOp">]> {
  let summary = "close the prover's transcript replica";
  let description = [{
    The dual of `oir.decide`: consumes the final sponge state and is
    the prover program's terminal operation. The prover decides
    nothing — acceptance belongs to verifiers; a prover run's success
    claim is only ever the emitted bytes.
  }];
  let arguments = (ins Oir_SpongeType:$sponge, Oir_SrcAttr:$src);
  let assemblyFormat = "$sponge (`src` $src^)? attr-dict";
}

#endif // ZKC_DIALECT_OIR_OPS_TD
