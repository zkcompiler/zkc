//===- PirOps.td - Protocol IR ops --------------------------*- tablegen
//-*-===//
// The pir operation vocabulary for the kernel carrier
// (docs/spec/kernel.md, docs/spec/carrier.md). The kernel's two geometries
// map onto two MLIR mechanisms:
//
//   spine (E, ≤, A)   — block order IS the total order ≤; events thread
//                        one builtin `token` value, so order is SSA data
//                        dependence, not convention;
//   claim flow (C, R) — claims are `!pir.claim` SSA values; the container
//                        verifier enforces exactly-one-def/exactly-one-use
//                        (LIN as structure, the handshake.func precedent).
//
// Verification placement (carrier.md §5): ODS carries per-op shape only;
// body layout, thread continuity, claim linearity, label uniqueness, and
// terminal check resolution are container verification; BIND/COV semantics are
// the seal pass. Inherent state is properties, discardable metadata is
// the attribute dictionary (carrier.md §9): the canonical encoder walks
// typed inherent state, so a foreign discardable attribute can never
// perturb identity. Only the `expr` trees and the kappa dictionary stay
// attributes — trees and maps are what attributes are for.
// Every protocol op writes the dialect's ProtocolResource:
// generic passes keep protocol content ordered and alive without special
// cases (checks and sinks have no results — the effect is what anchors
// them). Ops must never grow folders or canonicalization patterns: a fold
// would change the transcript a protocol's identity is computed from.
//===----------------------------------------------------------------------===//

#ifndef ZKC_DIALECT_PIR_OPS_TD
#define ZKC_DIALECT_PIR_OPS_TD

include "mlir/IR/EnumAttr.td"
include "mlir/IR/Properties.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "zkc/Dialect/Pir/PirInterfaces.td"
include "zkc/Dialect/Pir/PirTypes.td"

//===----------------------------------------------------------------------===//
// Effects. One resource covers all protocol content: events, checks, and
// sinks write it, so CSE never merges them, DCE never drops them, and
// motion passes treat them conservatively — defense in depth on top of
// token threading (carrier.md §3). The chain-safety regression is the
// empirical gate that this and the threading together keep generic
// pipelines byte-neutral.
//===----------------------------------------------------------------------===//

def Pir_ProtocolResource : Resource<"::zkc::pir::ProtocolResource">;

defvar Pir_ProtocolEffect = MemoryEffects<[MemWrite<Pir_ProtocolResource>]>;

// Every protocol member shares the effect, the container whitelist,
// and the member interface the container verifier walks (carrier.md
// §5): `overridden` names the defaulted interface methods this op
// implements beyond the mandatory getPhase. One point of change when
// a new container kind or member category is admitted.
class Pir_MemberOp<string mnemonic, list<string> overridden = [],
                   list<Trait> extraTraits = []>
    : Pir_Op<mnemonic,
             !listconcat([Pir_ProtocolEffect,
                          ParentOneOf<["ProtocolOp", "SealedOp"]>,
                          DeclareOpInterfaceMethods<
                              Pir_ProtocolMemberOpInterface, overridden>],
                         extraTraits)>;

// The spine-event override set: labeled, threaded, absorption-aware.
// Membership is a slot-only fact (carrier.md §4): message roles name
// prover messages, and other event kinds gain membership only with a
// consumer — until then the shape is unrepresentable, not rejected.
defvar Pir_SpineEventMethods = ["getMemberLabel", "getThreadIn", "getThreadOut",
                                "isAbsorbing"];

//===----------------------------------------------------------------------===//
// Enums
//===----------------------------------------------------------------------===//

// A public binding binds either at seal time or per instance. There is
// deliberately no realization stage: it would let one sealed artifact
// produce a different transcript per realization (kernel.md §2).
def Pir_Stage : I32Enum<"Stage", "public binding stage",
                        [I32EnumCase<"Seal", 0, "seal">,
                         I32EnumCase<"Instance", 1, "instance">]> {
  let cppNamespace = "::zkc::pir";
}
def Pir_StageProp : EnumProp<Pir_Stage>;

//===----------------------------------------------------------------------===//
// Sources (kernel.md §1.4). Sources produce claims and sit before the
// spine; they are graph nodes, not transcript events.
//===----------------------------------------------------------------------===//

def Pir_InstantiateOp : Pir_MemberOp<"instantiate", ["getMemberLabel"]> {
  let summary = "instantiate a claim from a contract statement";
  let description = [{
    The contract-backed source: produces one live claim carrying its
    descriptor **anchors** — identity strings keyed by the claim descriptor
    profile's exact anchor names (docs/spec/vocabularies.md §3);
    digest-valued anchors carry the `sha256:` reference prefix
    (kernel.md §8). Anchors are ids and digests, never relation bodies
    — the membrane (kernel.md §1.6). Exact agreement with the result
    type's descriptor profile is a seal judgment. The result is
    linear: the container verifier requires exactly one consumer, so
    the obligation this claim represents must reach a reduction or a
    terminal sink.
  }];
  let arguments = (ins StringProp:$label, DictionaryAttr:$anchors);
  let results = (outs Pir_ClaimType:$claim);
  let assemblyFormat = [{
    $label `anchors` $anchors `:` type($claim) attr-dict
  }];
  let hasVerifier = 1;
}

//===----------------------------------------------------------------------===//
// Spine events (kernel.md §1.1). Block order is ≤. Each threaded event
// consumes the previous event's token and produces the next; the
// container verifier requires the chain to be exactly the block order,
// so there is one spine and no zigzag. Absorption (membership in A) is
// an event property: bind and chal always absorb; slot absorbs unless
// `unabsorbed`; check never absorbs.
//===----------------------------------------------------------------------===//

def Pir_BeginOp : Pir_MemberOp<"begin", ["getThreadOut"]> {
  let summary = "spine head: produces the initial thread token";
  let results = (outs Token:$out);
  let assemblyFormat = "attr-dict";
}

def Pir_BindOp
    : Pir_MemberOp<"bind", Pir_SpineEventMethods, [InferTypeOpAdaptor]> {
  let summary = "public binding event (absorbing)";
  let description = [{
    Declares a public input or context binding as a spine event
    (kernel.md §1.1 public_bind): the binding is absorbed, so every later
    challenge is bound to it — the discipline whose absence is the weak
    Fiat-Shamir bug class. `payload_class` keys the value's codec in
    `kappa.codecs`. An instance-stage binding's value arrives as a
    statement argument at run time; a seal-stage binding carries its
    `value` explicitly and projects to a constant (a seal-stage bind
    without a value, or an instance-stage bind with one, is a seal
    error).
  }];
  let arguments = (ins Token:$thread, StringProp:$label,
      StringProp:$payload_class, Pir_StageProp:$stage,
      OptionalProp<StringProp>:$value);
  let results = (outs Token:$out, Pir_ValType:$val);
  let assemblyFormat = [{
    $thread $label `:` $payload_class `stage` $stage (`=` $value^)?
    attr-dict
  }];
}

def Pir_SlotOp
    : Pir_MemberOp<"slot",
                   !listconcat(Pir_SpineEventMethods, ["getMembership"]),
                   [InferTypeOpAdaptor]> {
  let summary = "prover-message event";
  let description = [{
    Proof material enters the verifier-visible stream. Produces the
    thread continuation and a freely-readable `!pir.val<class>` handle;
    both result types are inferred, so a mismatching handle class cannot
    be written. `unabsorbed` marks read-without-binding material (FRI
    authentication paths are the canonical case); by the kernel's default
    rule an unabsorbed slot may not precede any challenge — the
    generalized Frozen-Heart condition, checked at seal (kernel.md §5.2).
    `binding` is the slot's construction route
    (docs/spec/endpoints.md §6.2): what supplies the written
    value on the prover endpoint — "<instance>.<result-index>" for a
    hole-instance output, "bind:<name>" for a statement echo, or
    "const:<name>" for a kappa constant. Verifier projection ignores
    it; prover projection requires it. The canonical encoding normalizes
    `bind:`/`slot:`/`chal:`/`witness:` references to positions, so renaming
    those events is id-stable; a `<instance>.<n>` hole reference and a
    `const:<name>` reference carry their name into the encoding, so renaming
    a route instance or a kappa constant does change the id.
  }];
  let arguments = (ins Token:$thread, StringProp:$label,
      StringProp:$payload_class,
      DefaultValuedProp<StringProp, "\"1\"">:$count, UnitProp:$unabsorbed,
      OptionalProp<StringProp>:$instance, OptionalProp<StringProp>:$role,
      DefaultValuedProp<I64Prop, "0">:$idx, OptionalAttr<StrAttr>:$binding);
  let results = (outs Token:$out, Pir_ValType:$val);
  let assemblyFormat = [{
    $thread $label `:` $payload_class (`count` $count^)?
    (`unabsorbed` $unabsorbed^)?
    (`in` $instance^)? (`as` $role^)? (`idx` $idx^)?
    (`binding` $binding^)? attr-dict
  }];
  let hasVerifier = 1;
}

def Pir_ChalOp
    : Pir_MemberOp<"chal", Pir_SpineEventMethods,
                   [InferTypeOpAdaptor,
                    DeclareOpInterfaceMethods<
                        Pir_ChallengeCapabilityOpInterface,
                        ["getChallengeValue", "getChallengePayloadClass",
                         "getChallengeCount", "getChallengeSamplingRule"]>]> {
  let summary = "fresh-challenge event";
  let description = [{
    Samples a fresh challenge from the current transcript prefix
    (kernel.md §1.5, origin `fresh`). `deps` is the requirement set P_req
    as value operands: SSA dominance makes "requires a later event"
    unrepresentable, and seal checks that every dependency is absorbed —
    prefix satisfaction is exactly precedence plus absorption
    (kernel.md §5.1). `space` is the exact sample-space cardinality
    |C| as a minimal decimal string (no leading zeros, no fraction —
    kernel.md §3 item 4's spelling for large numerics), so one size has one
    spelling, identity stays bit-stable, and prime-order spaces are
    spellable; it is also the |C_i| a Soundness Kernel rule reads as a
    verified-by-use quantity (kernel.md §9). `payload_class` is the
    semantic class of each sample and keys its codec in `kappa.codecs`;
    challenge origin is carried by this operation, never by the retired
    `"chal"` pseudo-class.  The result handle therefore has type
    `!pir.val<payload_class>` by inference.

    `mode` realizes χ's reserved mode axis M (shape, sampling) for a
    challenge that departs the scalar default. Absent = one scalar sample
    under the uniform rule. Present =
    `["vector", count, sampling]`: the vector shape FRI's query round
    draws, `count` the identity-bearing sample multiplicity (ℓ) as a
    minimal decimal from 2 through 2^20 (a 1-vector is a second spelling of a scalar)
    priced beside the per-sample `space`, `sampling` an admitted rule
    (the (1−δ)^ℓ query bound assumes independent draws). Reuse class is
    a schema fact of the use, not a challenge fact, so it is not here
    (docs/spec/vocabularies.md §7).
  }];
  let arguments = (ins Token:$thread, Variadic<Pir_ValType>:$deps,
      StringProp:$label, StringProp:$payload_class, StringProp:$domain,
      StringProp:$space, OptionalProp<ArrayProp<StringProp>>:$mode);
  let results = (outs Token:$out, Pir_ValType:$val);
  let assemblyFormat = [{
    $thread (`deps` `(` $deps^ `:` type($deps) `)`)?
    $label `:` $payload_class `domain` $domain `space` $space
    (`mode` $mode^)? attr-dict
  }];
  let hasVerifier = 1;
}

def Pir_CheckOp : Pir_MemberOp<"check", ["getMemberLabel"]> {
  let summary = "verifier check event (non-absorbing)";
  let description = [{
    A verifier-side predicate over event value handles: a spine event that
    never advances the transcript (kernel.md §1.2). `contract` is a
    human-readable CheckContract lookup and diagnostic handle; seal resolves
    it and projection carries the exact CheckContract content digest as
    semantic/dispatch authority. Neither field attests an executable adapter
    implementation. `params`
    supplies the contract's static parameter map;
    `semantic_args` binds its intrinsic semantic roles. Contract resolution,
    exact parameter/role agreement, operand segmentation, and mode are seal
    checks. `expr` is the optional transparent interior: an inert
    canonical expression tree with `eq` at the root over leaves
    ["in", k] (input reference) / ["const", name] (kappa.constants
    reference) and algebra nodes [op, args...] — data, never
    operations, so the optimizer cannot touch the declared equation;
    absent keeps the check opaque. There is deliberately no statement
    leaf: binds produce vals, so statement values reach checks as SSA
    inputs and are therefore always absorbed. A terminal rule selects checks
    by role and label; canonical form replaces those labels by event
    positions.
  }];
  let arguments = (ins Variadic<Pir_ValType>:$inputs, StringProp:$label,
      StringProp:$contract, OptionalAttr<DictionaryAttr>:$params,
      OptionalAttr<DictionaryAttr>:$semantic_args,
      OptionalAttr<ArrayAttr>:$expr);
  let assemblyFormat = [{
    $label `contract` $contract (`params` $params^)?
    (`semantic_args` $semantic_args^)?
    (`(` $inputs^ `:` type($inputs) `)`)?
    (`expr` $expr^)? attr-dict
  }];
}

def Pir_EndOp : Pir_MemberOp<"end", ["getThreadIn"]> {
  let summary = "spine terminator: the proof stream is exhausted";
  let description = [{
    Consumes the final thread token. Projection realizes it strictly
    (`expect_end`): trailing proof bytes change the accept set and are
    never an implementation detail (docs/spec/endpoints.md §3).
  }];
  let arguments = (ins Token:$thread);
  let assemblyFormat = "$thread attr-dict";
}

//===----------------------------------------------------------------------===//
// Transformers (kernel.md §1.4, carrier.md §4). One generic op: the
// reduction contract is registry data keyed by `contract`
// — a new reduction family is a registry row, never a recompile. Reduces sit
// after `end`, so SSA dominance proves every consumed challenge was
// sampled before the reduction is formed; body events reference the
// instance through membership props (forward references the container
// verifier resolves in a second pass).
//===----------------------------------------------------------------------===//

def Pir_ReduceOp
    : Pir_MemberOp<"reduce", ["getMemberLabel"], [AttrSizedOperandSegments]> {
  let summary = "reduction: consumes claims, produces claims";
  let description = [{
    A reduction instance (kernel.md §1.4): consumes one or more claims
    plus positional value dependencies (dep operand i binds the
    contract shape's dep slot i — challenges and objects), produces one or
    more claims. Output descriptor profiles are spelled in the result types,
    never inferred: they are registry data, unavailable at parse and
    forbidden in verifiers (registries are IO); the seal pass cross-checks
    profiles and arities against the ReductionContract. The contract contains
    both the reduction shape and its semantic implication. It carries no
    security analysis: which theorem applies here is a property of a
    derivation, not of the protocol, so it is named by a derivation term and
    never by this operation (docs/spec/soundness.md §1). `checks` maps
    every contract role to one check label in this container. Labels are
    authored selectors only: canonical encoding replaces them with event
    positions. `params` is the contract-instance parameter dictionary (values
    in the kernel encoding domain). `out_anchors` carries one authored anchors
    assertion per result claim, positional with the results; seal derives the
    expected values from the contract and requires exact agreement
    (docs/spec/vocabularies.md §3).
  }];
  let arguments = (ins Variadic<Pir_ClaimType>:$claims,
      Variadic<Pir_ValType>:$deps, StringProp:$label, StringProp:$contract,
      DictionaryAttr:$checks, OptionalAttr<DictionaryAttr>:$params,
      OptionalAttr<ArrayAttr>:$out_anchors);
  let results = (outs Variadic<Pir_ClaimType>:$outs);
  let assemblyFormat = [{
    $label `contract` $contract
    `(` $claims `:` type($claims) `)`
    (`deps` `(` $deps^ `:` type($deps) `)`)?
    `checks` $checks (`params` $params^)? (`anchors` $out_anchors^)?
    `->` type($outs) attr-dict
  }];
  let hasVerifier = 1;
}

//===----------------------------------------------------------------------===//
// Semantic material attachments. These identity-bearing edges connect a
// local verifier-visible SSA value to a stable semantic reference. They are
// neither transcript events nor claim transformations, and therefore occupy
// their own tail phase after reductions and before terminal sinks.
//===----------------------------------------------------------------------===//

def Pir_MaterialBindOp : Pir_MemberOp<"material_bind"> {
  let summary = "bind a verifier value to a stable semantic reference";
  let description = [{
    Records one identity-bearing `ValueRef -> SemanticMaterialRef` edge.
    `value` supplies the local endpoint through SSA/canonical position;
    `semantic_ref` is the globally stable digest-shaped endpoint preserved by
    link. Container verification requires at most one edge per SSA value and
    reverse-injectivity of semantic references. Semantic closure additionally
    requires every edge to be consumed by an admitted terminal attachment.
    There is deliberately no alias operation in this carrier version.
  }];
  let arguments = (ins Pir_ValType:$value, StringProp:$semantic_ref);
  let assemblyFormat = [{
    $value `to` $semantic_ref `:` type($value) attr-dict
  }];
}

//===----------------------------------------------------------------------===//
// Terminal sinks (kernel.md §1.4). Exactly one per consumed claim; which
// kinds are permitted is SealPolicy, checked at seal. Sinks sit after
// the spine: routing is decided about the whole protocol, not
// interleaved with it.
//===----------------------------------------------------------------------===//

// The routed sinks share one shape; discharge is its own def because its
// terminal justification is a rule plus role-bound checks, not a route.
class Pir_RoutedSinkOp<string mnemonic> : Pir_MemberOp<mnemonic> {
  let arguments = (ins Pir_ClaimType:$claim, StringProp:$route);
  let assemblyFormat = "$claim `:` type($claim) `route` $route attr-dict";
}

def Pir_DischargeOp : Pir_MemberOp<"discharge"> {
  let summary = "terminal route: the claim is proven";
  let description = [{
    Discharges one claim through the resolved TerminalRule named by `rule`.
    `checks` maps every terminal role to one check label in this container.
    The mapping is exact rule input, not an unordered citation set: values
    must resolve, be injective within the discharge, and be selected by at
    most one discharge in the whole artifact. Labels are selectors only;
    canonical encoding uses check event positions.
  }];
  let arguments = (ins Pir_ClaimType:$claim, StringProp:$rule,
      DictionaryAttr:$checks);
  let assemblyFormat = [{
    $claim `:` type($claim) `rule` $rule `checks` $checks attr-dict
  }];
}

def Pir_ExportOp : Pir_RoutedSinkOp<"export"> {
  let summary = "terminal route: the obligation leaves this artifact";
}

def Pir_AssumeOp : Pir_RoutedSinkOp<"assume"> {
  let summary = "terminal route: accepted under an explicit assumption";
}

def Pir_ResidualOp : Pir_RoutedSinkOp<"residual"> {
  let summary = "terminal route: an explicit non-closed leftover";
}

//===----------------------------------------------------------------------===//
// Containers (carrier.md §6). The artifact — never a loose body — is the
// unit of identity and verification. Body layout is fixed:
//
//   [sources]* begin [spine events]* end [reduces]* [material bindings]*
//   [sinks]*
//
// so the canonical encoder's walk order is the block order (the tail
// is normalized at seal before encoding, carrier.md §6), and the two
// geometries read off one block. Sealed artifacts carry no materialized
// tables: tabulations of E, χ, C, K are views computed on demand
// (kernel.md §11) — there is no mirror to drift.
//===----------------------------------------------------------------------===//

class Pir_ContainerOp<string mnemonic, list<Trait> extraTraits = []>
    : Pir_Op<mnemonic, !listconcat([IsolatedFromAbove, NoRegionArguments,
                                    NoTerminator, SingleBlock],
                                   extraTraits)> {
  let regions = (region SizedRegion<1>:$body);
  let hasVerifier = 1;
}

def Pir_ProtocolOp : Pir_ContainerOp<"protocol"> {
  let summary = "open protocol under construction";
  let description = [{
    An open protocol: editable, not yet an artifact. `kappa` is the
    construction profile (codecs, sponge, sampling, iv policy);
    `policy` names the SealPolicy mode the seal boundary will enforce.
    `vocab` is the resolved-vocabulary table — every cited descriptor
    profile, CheckContract, ReductionContract, and TerminalRule mapped to its registry content
    (kernel.md §8: vocabulary citations resolve to content). The seal
    stamps it immediately before encoding; an authored protocol
    normally carries none, and without it there is no canonical
    identity. `segments` is the spine's segment decomposition
    (kernel.md §5.3): the event positions where later segments start
    — absent means one segment; link records the splice points. It is
    judgment-bearing (the statement-binding default is judged per
    segment) and therefore identity-bearing. A protocol carries no
    security analysis: a conditional security judgment is derived about a
    sealed protocol rather than declared inside it, so no theorem citation
    is protocol content (docs/spec/soundness.md §1). Containers are
    content-addressed after sealing and never symbol-referenced;
    `protocol_name` is a human handle, not an identity.
  }];
  let arguments = (ins StringProp:$protocol_name,
      OptionalAttr<DictionaryAttr>:$kappa, OptionalAttr<DictionaryAttr>:$vocab,
      OptionalAttr<DictionaryAttr>:$routes,
      OptionalProp<ArrayProp<I64Prop>>:$segments,
      DefaultValuedProp<StringProp, "\"closed_proof\"">:$policy);
  let assemblyFormat = [{
    $protocol_name (`kappa` $kappa^)? (`vocab` $vocab^)?
    (`routes` $routes^)? (`segments` $segments^)? (`policy` $policy^)?
    attr-dict-with-keyword $body
  }];
}

def Pir_SealedOp : Pir_ContainerOp<"sealed"> {
  let summary = "sealed protocol artifact (immutable)";
  let description = [{
    The closed artifact produced by the seal boundary: same body shape
    as `pir.protocol`, plus the canonical identity `id` — the SHA-256 of
    the canonical encoding of body, kappa, vocabulary table, and policy
    (kernel.md §8). `vocab` maps every cited descriptor profile,
    CheckContract, ReductionContract, and TerminalRule to the content digest of the registry
    entry the seal consumed, so
    a shadow vocabulary entry at the same name cannot survive under
    the sealed id; the recheck pass re-judges the table against its
    loaded registries. Sealed artifacts are never rewritten in place; a
    semantic change is a new artifact. The id is recomputed and
    compared fail-closed by the artifact loader, and the rewrite guard
    refuses pattern application rooted under this op with an audit
    remark.
  }];
  let arguments = (ins StringProp:$protocol_name, StringProp:$id,
      OptionalAttr<DictionaryAttr>:$kappa, OptionalAttr<DictionaryAttr>:$vocab,
      OptionalAttr<DictionaryAttr>:$routes,
      OptionalProp<ArrayProp<I64Prop>>:$segments,
      DefaultValuedProp<StringProp, "\"closed_proof\"">:$policy);
  let assemblyFormat = [{
    $protocol_name `id` $id (`kappa` $kappa^)? (`vocab` $vocab^)?
    (`routes` $routes^)? (`segments` $segments^)? (`policy` $policy^)?
    attr-dict-with-keyword $body
  }];
}

#endif // ZKC_DIALECT_PIR_OPS_TD
