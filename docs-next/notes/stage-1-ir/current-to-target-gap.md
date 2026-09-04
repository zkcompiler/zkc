# Current-to-target Protocol IR architecture gap

> **Document kind:** Temporary Stage 1 architecture correspondence map
> **Document state:** Stage 1 conclusion companion
> **Authority:** None. This page compares observed current correspondence and
> an earlier lifecycle hypothesis with the selected non-normative target. The
> current specifications under [`docs/`](../../../docs/README.md) retain their
> authority until an explicit normative cutover.
> **Scope:** Architectural deltas only. This is not a defect, vulnerability,
> implementation-status, or conformance report.
> **Disposition:** Retain under `notes/` while the v0 architecture is being
> absorbed into durable owners, then remove it with the other temporary Stage 1
> research notes.

## 1. Comparison basis

This map compares three snapshots:

1. the specification/code correspondence reconstructed in
   [Current zkc Protocol IR correspondence](cases/current-zkc-correspondence.md);
2. the earlier coherent but now superseded
   [Protocol subject and lifecycle candidate](../../pir/protocol-lifecycle.md);
   and
3. the selected Stage 1
   [Protocol IR architecture](../../project/protocol-ir-architecture.md).

The first snapshot records what the present design and implementation make
observable. The second records the strongest prior factorization before Stage
1 was reopened. The third is the ideal target selected after the reopened
research; it is not constrained to preserve either predecessor's layout or
identity choices.

This page answers only:

> Which architectural commitments survive, which become more precise, and
> which are deliberately replaced by the selected target?

It does not answer how to migrate artifacts, APIs, tests, source files, or
identities. It does not authorize implementation, normative migration, or
Stage 2 work.

## 2. Disposition vocabulary

Each axis receives one primary disposition:

| Disposition | Meaning in this map |
|---|---|
| **Preserved** | The present architectural direction remains a target invariant, although its terminology may be sharpened. |
| **Refined** | The existing concern remains, but the target assigns a more exact owner, boundary, or law. |
| **Replaced** | A current or earlier provisional architectural choice is not the selected target. |
| **New** | The target introduces a first-class subject or invariant absent from the current and earlier models. |
| **Deferred** | Stage 1 fixes the surrounding boundary but intentionally leaves the exact mechanism to a later design owner. |

“Replaced” does not mean that the current mechanism is erroneous. It means
that it no longer supplies the ideal semantic decomposition selected for v0.
Likewise, “preserved” is not an implementation-conformance claim.

## 3. Executive delta ledger

| Axis | Current correspondence | Earlier lifecycle candidate | Selected target | Primary disposition |
|---|---|---|---|---|
| Outer semantic boundaries | Protocol, judgments, OIR, relations, and realization are distinct subjects | Preserved those subjects and capability boundaries | Retains the same separation and makes dependent subjects explicit | **Preserved** |
| Internal Protocol factorization | One identified PIR root combines verifier semantics, transcript construction, policy, and usually prover routes | One abstract `ProtocolRoot` above its PIR carrier; internal fields remained largely co-owned | `Protocol = InteractiveCore + ChallengeInterpretation`; Interface and ProverPlan are dependent siblings | **Replaced** |
| Observable order | Block order, phase rules, and a threaded Protocol effect establish a total event spine | Continued to treat ordered content as part of the root, without fixing the exact semantic owner | One identity-bearing total observable schedule belongs to `InteractiveCore`; partial order exists only before canonicalization | **Refined** |
| External interface | Some ABI labels survive in the carrier and affect OIR or relation wiring despite being erased from `ProtocolId` | Recognized the pressure but deferred “inside Protocol, separate Interface, or canonical positions” | `ProtocolInterfaceId` is a separate dependent identity over an exact `ProtocolId` | **New** |
| Prover construction | Construction routes and witness-facing declarations normally enter Protocol identity | Retained them in the root while naming future separation as a reopening condition | `ProverPlanId` is a separate dependent identity; Protocol keeps abstract prover obligations | **Replaced** |
| Semantic regime | Admission depends on intrinsic meanings that are mostly process- or build-local | Regime qualified admission but deliberately did not enter `ProtocolId` | Family-typed regimes qualify semantic identity encodings; changed meaning cannot silently retain an ID | **Replaced** |
| Authoring versus canonical IR | Open and sealed PIR largely share one dialect and body schema | PIR remained both authoring surface and sole v0 carrier; canonical form was an internal identity projection | Rich authoring/import dialects elaborate into one small closed canonical PIR level | **Replaced** |
| Canonical form | `pir.sealed` may preserve distinct authored bodies with one quotient-based `ProtocolId` | `CanonicalProtocolForm` was deterministic identity material, not supported ingress or a required physical graph | One legal canonical semantic graph exists per regime and Protocol, modulo carrier trivia and SSA alpha-renaming | **Replaced** |
| Event obligation completeness | Most events derive obligations, but sealed reserved syntax may lack a projection-obligation rule | Left the admission grade versus unsupported-event choice unresolved | Every canonical event kind has an abstract endpoint obligation; target support remains a later projection decision | **Refined** |
| Effects and reorderability | One global Protocol resource conservatively prevents movement, while the ordered spine carries semantic order | Identified the blanket resource as a policy/semantics question | Protected observation classes and named trace relations govern legality; exact MLIR effect encoding is later work | **Refined** |
| Composition | Linking joins open subjects at faces and returns another open proposal | Preserved ordinary reseal and left policy composition open | Composition creates a new Core with occurrence namespaces, face maps, causal seams, total interleaving, and challenge/domain choices | **Refined** |
| Admission authority | Decode, authentication, admission, mutation, and consumer access are distinct; admitted handles are opaque | Made the process-local capability contract explicit | Retains the same lifecycle authority separation around the closed canonical level | **Preserved** |
| Checker input | Native admission consumes PIR plus environment; the Python model is differential evidence, not a supported ingress checker | Deferred a stable independent ingress until a real consumer existed | Full v0 admission consumes restricted canonical MLIR, dependency preimages, regime semantics, identity encoder, and whole-object checker only | **Refined** |
| Transport and compatibility | MLIR bytecode persists PIR; semantic identity is not text or bytecode; no stable canonical-JSON contract | Kept MLIR as the sole v0 carrier and deferred a second representation | Keeps an exact fail-closed v0 with no historical compatibility promise; neutral package or compatibility dialect waits for explicit triggers | **Preserved** |

The largest discontinuity is therefore not the continued use of MLIR. It is
the replacement of a lifecycle-centered, quotient-identified PIR object with
a distinct authoring level and a closed canonical Protocol level whose
semantic subjects and dependent identities are explicitly factored.

## 4. Subject factorization

### 4.1 What survives

The current architecture already establishes the most important outer
separations:

- a Protocol is not an OIR endpoint program;
- a structural or semantic admission result is not a soundness,
  completeness, or correspondence judgment;
- a relation attachment does not retroactively change the Protocol;
- a runtime supplier or successful execution does not mint Protocol
  authority; and
- a checked compiler successor is a newly authenticated subject, not a
  mutation that inherits admission.

Those separations are preserved. Purpose-specific consumer views also remain
derived from admitted authority rather than producer-authored mirrors.

### 4.2 What is replaced

The internal root changes from a broad artifact-shaped aggregation to a
semantic factorization:

```text
InteractiveCore
  + ChallengeInterpretation
  = Protocol

ProtocolId
  + ProtocolInterface
  -> ProtocolInterfaceId

ProtocolId
  + ProverPlan
  -> ProverPlanId
```

The `InteractiveCore` owns verifier-visible interaction: typed semantic ports,
events, challenges as fresh public-coin occurrences, claim and reduction flow,
checks, failures, terminal behavior, abstract prover obligations, causal
dependencies, and the selected total observable schedule.

The `ChallengeInterpretation` then selects fresh public coins or one exact
Fiat--Shamir transcript construction. Fresh-coin and Fiat--Shamir forms over
one Core are different Protocols related by an `FSCompile` judgment rather
than two representations of one identity.

This replaces the earlier tendency to let a carrier-shaped `ProtocolRoot`
co-own verifier semantics, transcript construction, interface residue, and
prover construction. The outer Protocol boundary is preserved; its internal
semantic algebra is replaced.

## 5. Total schedule ownership

The present ordered effect spine is retained as strong design evidence. The
target does not reinterpret an interactive protocol as an unordered graph
that gains order only during Fiat--Shamir lowering.

The ownership is refined as follows:

- causal dependencies define mandatory precedence;
- `InteractiveCore` also owns one selected total observable schedule extending
  that precedence;
- the selected schedule participates in `CoreId`;
- a different linear extension normally denotes a different Core;
- partial-order authoring denotes a family or scheduling problem upstream;
  and
- genuine within-batch unorderedness requires an explicit aggregate event,
  not an implicit quotient over swapped observable events.

Current block order and token structure may correspond to this schedule, but
the target invariant is semantic and independent of their exact MLIR spelling.

## 6. ProtocolInterface

The current correspondence establishes that `ProtocolId` alone is not a
closed input to interface-sensitive consumers: relabel-invariant PIR can still
project to differently identified OIR or select different relation wiring.
The earlier candidate correctly exposed the pressure but left three choices
open.

Stage 1 now selects a separate dependent subject:

```text
ProtocolInterfaceId = identify(
  InterfaceSemanticRegimeId,
  ProtocolId,
  canonical_interface)
```

A Protocol Interface may bind canonical semantic ports to external ABI names,
positions, entry points, pre-Protocol value packaging, and explicit malformed
input behavior. It cannot change semantic public values, proof-event order,
transcript-observed encodings, challenges, checks, claims, or terminal
outcomes. A field that changes those properties belongs to the Protocol.

This is a new first-class subject, not a request to move every current label
into a new object mechanically. It establishes the rule that OIR projection
and external correspondence consume an exact `ProtocolInterfaceId` instead of
unidentified carrier residue.

## 7. ProverPlan

The current PIR root normally identifies construction routes, witness-facing
declarations, and hole plans with verifier-visible behavior. The earlier
candidate retained that choice while treating independently evolving plans as
a possible reason to reopen it.

The selected target makes the separation unconditional:

- Protocol owns verifier-visible messages, their distributions, transcript
  actions, proof ABI, checks, accepted language, and abstract prover
  obligations;
- ProverPlan owns witness/construction DAGs, plan-local algorithms,
  scheduling, buffering, permitted private dependencies, supplier
  requirements, and explicit typed holes;
- `ProverPlanId` commits to the exact `ProtocolId`; and
- `PlanRealizes` and qualified completeness judgments connect the subjects
  without merging their identities.

If a supposed plan change alters a verifier-visible observation, it is a
Protocol change. This replaces construction-plan ownership inside the broad
Protocol root while preserving the requirement that the Protocol itself be
complete enough to state prover obligations.

## 8. Semantic regimes and identity

The current design already needs an interpretation context beyond raw carrier
bytes. The earlier candidate called this a `SemanticRegime`, but treated it as
an admission qualifier that did not enter `ProtocolId` and might remain
process- or build-local.

The target replaces that rule. Semantic regimes are stable, typed inputs to
semantic identities. At minimum, the architecture distinguishes Protocol,
Interface, and ProverPlan regimes rather than forcing all subjects under one
tool release number. A regime owns the operation and contract meanings,
protected observations and intrinsic effects, framing and sampling semantics,
dependency-schema interpretation, admission rules, and identity-encoding
domain for its subject family.

Consequently:

- identical carrier bodies under different semantic meanings do not denote
  the same semantic subject;
- tool release, MLIR bytecode version, producer marker, local policy, and
  semantic regime remain different axes;
- a carrier revision may preserve a semantic ID only by decoding to the same
  canonical subject under the same regime; and
- a semantic change requires a new identity or an explicit checked relation.

The exact identifier grammar and hash construction remain normative-schema
work. Their architectural preimage boundaries are no longer open.

## 9. Authoring and canonical levels

### 9.1 Current and earlier posture

Open and sealed PIR currently reuse one dialect and nearly the same authored
body. MLIR provides valuable SSA, ordering, operation interfaces, effects,
verification, diagnostics, transformation support, and persistence, while
zkc-owned whole-object logic supplies canonical indexing, sealing, and
projection.

The earlier candidate retained PIR as both the sole v0 authoring surface and
persistence carrier. It introduced an abstract `ProtocolRoot` and an internal
canonical identity projection, but declined to introduce another concrete IR
or supported ingress.

### 9.2 Selected boundary

The target keeps MLIR but replaces the one-level posture:

```text
rich, possibly mixed-dialect AuthoringUnit
  -> exhaustive elaboration, closure, and normalization
  -> closed canonical PIR graph
  -> authentication
  -> whole-Protocol admission
  -> opaque AdmittedProtocol
```

Authoring may be partial, family-valued, macro-rich, or only causally ordered.
Canonical PIR denotes exactly one Protocol. It contains only its closed
vocabulary and an explicit minimal carrier allowlist, with no unresolved
choice, authoring macro, plan data, interface label, foreign semantic op, or
arbitrary metadata.

Lifecycle authority states do not each require a dialect. Draft, decoded,
authenticated, and admitted states remain types or capabilities around
subjects. The dialect-level distinction is semantic: rich authoring meaning
versus the closed canonical Protocol assembly level.

## 10. Physical normal form

Current `pir.sealed` is an identified representative of a semantic quotient:
two carrier bodies may preserve different erased labels or authored order
while sharing canonical identity bytes. The earlier candidate kept this model
and made `CanonicalProtocolForm` an internal identity projection rather than a
required physical form.

The target replaces it with a canonical semantic graph contract:

- one regime and one Protocol admit one legal canonical PIR operation graph;
- equivalence is limited to MLIR object identity, SSA alpha-renaming, and
  explicitly excluded transport or diagnostic trivia;
- defaults, positions, ordered fields, and unordered collections have fixed
  normalized forms;
- every attribute is classified;
- the specified semantic encoder is bijective with the legal canonical graph
  modulo the allowed carrier trivia; and
- MLIR text, allocation, printer output, and bytecode need not be unique.

MLIR's generic canonicalizer does not define this contract. Dialect-conversion
legality may prove that authoring operations disappeared, but zkc's
whole-Protocol checker owns semantic closure and admission.

The target therefore selects physical semantic normal form without confusing
it with byte-identical serialization.

## 11. Admitted event obligation completeness

The current event model aims to derive endpoint obligations from Protocol
events, yet reserved syntax can be structurally sealed while having no
obligation-derivation or projection case. The earlier candidate left open
whether such a subject was authoring-only, explicitly non-executable, or part
of a weaker admission grade.

The target refines the admission contract:

> Every event kind admitted into canonical PIR has a complete abstract
> endpoint-obligation rule.

This does not require every target to implement every event. It separates two
questions:

1. **source completeness:** the canonical Protocol defines the abstract
   obligation of every event; and
2. **target projectability:** one exact endpoint target may support or refuse
   that obligation.

An event whose abstract obligation is not yet defined remains authoring-only.
It cannot enter the generic endpoint-ready admitted Protocol merely because
its local carrier structure verifies.

## 12. Effects and checked transformations

The current global `ProtocolResource` usefully blocks generic motion, common
subexpression elimination, dead-code elimination, and speculation. It is also
more conservative than the semantic differences among transcript, wire,
check, claim, artifact, and terminal observations.

The target refines the semantic rule around explicit protected observation
classes:

```text
TRANSCRIPT  WIRE  PUBLIC  CHECK  ARTIFACT  CLAIM  TERMINAL
```

SSA independence or algebraic purity alone does not authorize reordering an
action observed by any protected class. Transformations state a named relation
appropriate to the claim, including `RepresentationEq`, `CoreEq`,
`ProtocolEq`, observer-indexed `TraceEq`, `TraceRefines`, distributional
equality or closeness, `FSCompile`, `ProjectionCorrect`, `PlanRealizes`,
`PropertyTransport`, and `IntentionalChange`. Cost comparison remains
orthogonal.

The exact MLIR effect resources, local commutation interfaces, validation
algorithms, and certificate formats are **deferred**. The semantic
observation classes and the prohibition on unqualified “semantic
equivalence” are selected now.

## 13. Composition

Current linking takes open subjects, identifies faces, and returns another
open proposal that must be sealed normally. Those lifecycle properties are
preserved. The target refines what the new proposal must eventually denote:

- tagged occurrence namespaces, including repeated instances of one child;
- explicit child-to-composite port and claim face maps;
- causal seams and one selected total interleaving;
- independent, shared, or derived challenge policy;
- transcript and construction domain separation;
- failure and terminal propagation; and
- recomputed dependency and endpoint-obligation closure.

Composition constructs a new `InteractiveCore` and therefore a new `CoreId`;
fresh-coin or Fiat--Shamir interpretation is selected afterward. It is not
plain graph union, event-list concatenation, or identity inheritance.

The complete composition algebra, property-transport rules, endpoint descent,
recursion, and IVC semantics are **deferred**. The minimum subject and
identity skeleton is selected.

## 14. Checker inputs and authority

### 14.1 Preserved authority model

The current implementation's separation of open content, sealed carrier,
persisted bytes, decoded artifact, admitted artifact, mutable reopening, and
derived consumer views remains target architecture. In particular:

- a root mnemonic or stored identity does not confer admission;
- decoding and identity authentication do not replace semantic admission;
- serialization does not carry a process-local capability;
- mutation or reopening discards admission; and
- consumers receive opaque admitted capabilities or purpose-specific views.

### 14.2 Refined independent boundary

The target fixes canonical MLIR PIR as the v0 full-admission ingress. A bounded
checker needs:

1. restricted MLIR core decoding;
2. the closed canonical PIR grammar;
3. the applicable semantic regime;
4. the semantic identity encoder;
5. the exact typed dependency manifest and required preimages;
6. an exact dependency resolver; and
7. the whole-Protocol admission rules.

It does not need authoring dialects, optimizer passes, search strategies, OIR
backends, realization code, or the full compiler environment. An expected
semantic ID, when supplied by the caller, is an assertion to authenticate;
transport bytes or a producer flag are not semantic authority.

Purpose-specific persisted views or certificates remain justified only by a
named consumer and an exact claim. In particular, source-free OIR can establish
its own identity and local validity, but source-relative projection coverage
requires the admitted source or sufficient source-bound evidence.

## 15. Compatibility and representation evolution

The target preserves the decision not to publish a second complete carrier or
a historical compatibility promise in v0. It sharpens the version axes so
that semantic regime, identity encoding, canonical PIR schema, MLIR transport,
dependency schemas, local policy, dependent-subject schemas, and producer
release cannot be collapsed into one version.

The resulting rule is exact and fail-closed:

- unknown canonical semantics are refused rather than ignored;
- decoder success establishes neither semantic preservation nor admission;
- a transport update preserves semantic identity only if it decodes to the
  same canonical subject under the same regime;
- a changed semantic subject receives a new identity or an explicit checked
  migration judgment; and
- the current identity encoding is not automatically a supported external
  interchange format.

A portable package or compatibility dialect remains **deferred** until a
concrete boundary demands it, such as an independently released non-MLIR
consumer, a declared long-lived artifact-retention window, independent
producer and consumer release cycles, a deployment constraint excluding MLIR,
or a formal extraction boundary requiring a stable neutral package.

That future representation would require an owned schema, upgrade rules,
independent decoders or checkers, and an explicit compatibility window. None
is implied or authorized by the Stage 1 selection.

## 16. Consolidated preservation and replacement boundary

The target should be read as preserving these architectural assets:

- MLIR as the primary v0 workbench and canonical structural carrier;
- explicit ordered interaction and linear claim/reduction flow;
- semantic identities independent of MLIR text and bytecode;
- fail-closed whole-object admission;
- opaque immutable admitted capabilities;
- separate Protocol, judgment, OIR, relation, and realization authorities;
- checked, identity-aware successor construction; and
- explicit asymmetric endpoint projection.

It replaces these provisional commitments:

- one nearly uniform PIR dialect for both rich authoring and admitted
  canonical content;
- quotient-only sealing over authored carrier bodies;
- a broad root that normally identifies prover construction with verifier
  behavior;
- an unresolved or implicit external interface input;
- process-local regime qualification outside semantic identity; and
- an ordered block whose several roles are not assigned to distinct semantic
  owners.

It introduces these first-class commitments:

- `InteractiveCore`, `ChallengeInterpretation`, and exact `Protocol`
  factorization;
- dependent `ProtocolInterfaceId` and `ProverPlanId` subjects;
- a closed physical canonical semantic graph;
- obligation-complete admitted event semantics;
- typed semantic regimes in identity preimages;
- protected observation classes and named transformation relations; and
- a minimum non-splicing composition skeleton.

It deliberately defers exact schemas, algorithms, operation spellings,
effect-interface implementation, checker packaging, composition algebra,
compatibility machinery, and proof-assistant representation.

## 17. Non-authorization boundary

This map is a Stage 1 research artifact. It authorizes none of the following:

- implementation changes;
- migration sequencing;
- source-file, dialect, operation, attribute, or API renames;
- artifact or identity conversion;
- compatibility promises or legacy decoders;
- normative edits under `docs/`;
- Stage 2 transition design; or
- claims that the current implementation already realizes the selected
  architecture.

Any later work must begin from an explicit authorization and the Stage 2 entry
contract in the selected architecture decision. Until then, the selected
target and current implementation remain deliberately separate descriptions.
