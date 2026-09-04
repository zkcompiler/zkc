# Current zkc Protocol IR correspondence

> **Document kind:** Temporary implementation-correspondence dossier
> **Document state:** First static research pass
> **Authority:** None. Current specifications retain normative authority; source
> and tests are implementation evidence. This dossier records architecture
> pressures and correspondence seams, not defects, vulnerabilities, or status
> claims.
> **Method:** Read-only inspection of specifications, source, and fixtures. The
> fixtures were inspected but not executed during this pass.
> **Disposition:** Use the verified pressures in Stage 1 candidate evaluation,
> promote resolved conclusions to their owners, then delete this page.

## 1. Executive result

The current model has a coherent semantic center, but PIR currently performs
at least three jobs:

1. editable authoring and compiler workbench;
2. carrier of an admitted representative of one Protocol identity; and
3. source of endpoint- and relation-facing interface data.

Those jobs are not closed under one identity relation. The most urgent native
questions are therefore:

- what exact subject `ProtocolId` identifies;
- whether external interface data is inside that subject or separately
  identified;
- whether “canonical” means a physical normal form or an encoded quotient;
- whether every sealed event has a complete projection-obligation status;
- whether prover construction plans belong to verifier Protocol identity;
- which semantic regime makes a long-lived ID meaningful; and
- which effect constraints are semantics versus conservative workbench policy.

The ordered effect spine, linear claim flow, separate judgments, and admitted
capability lifecycle remain strong evidence. This dossier does not decide how
they are distributed across authoring, canonical, interface, construction,
view, or carrier layers.

## 2. Current subject ledger

| Role | Current meaning | Authority or identity |
|---|---|---|
| Abstract Protocol | Ordered semantic events coupled to typed claims, reductions, checks, bindings, and terminal behavior | Kernel semantic subject; cross-geometry rules make sequence and claim graph co-authoritative |
| Open PIR | Editable proposal, possibly unresolved | No admitted Protocol authority |
| Resolved seal candidate | Open PIR temporarily paired with exact cited vocabulary selected from the environment | Ephemeral input to seal |
| Raw `pir.sealed` | MLIR operation containing stored ID, cited vocabulary, policy, and the authored body | Carrier representative claiming identity; a new boundary must still authenticate and admit it |
| `ProtocolId` | Hash of zkc's canonical positional semantic encoding | Excludes MLIR text/bytecode and most labels; identifies an equivalence class of carrier representatives |
| Persisted artifact | MLIR bytecode containing one sealed root | Transport; version and producer metadata support decoding, while identity is recomputed independently |
| Decoded artifact | Private immutable storage after decode, structure checks, and ID authentication | Not yet registry-backed semantic admission |
| Admitted artifact | Decoded subject rechecked under one immutable `ProtocolEnvironment` | Process-local capability; mutable reopening loses authority |
| Projection obligations | Per-event endpoint duties derived from Protocol | Derived view; no separate stored truth |
| Analysis facts and judgments | Owned facts derived from admitted PIR, then qualified property results | Separate subject, signature, rules, assumptions, and plan |
| Compiler observation | Protocol ID, facts, and endpoint-relevant measurements under exact compiler semantics | Artifact-neutral Compiler Core delegates PIR authority to a provider |
| Checked successor | Reopened, changed, resealed, re-admitted Protocol plus a checked relation | Normally a fresh Protocol identity |
| OIR | One asymmetric endpoint program with source provenance | Separate OIR identity and a provenance-erased semantic digest |
| Relation correspondence | Post-seal interpretation under one RelationContract | Contract and judgment have separate identities; Protocol is not retroactively changed |
| Realization and execution | Supplier-, target-, and instance-bound endpoint behavior | Operational observations never mint upstream semantic authority |
| Linked Protocol | Result of combining two judged open subjects at named faces | New open proposal, later sealed normally |

Primary current owners include the
[kernel](../../../../docs/spec/kernel.md),
[carrier](../../../../docs/spec/carrier.md),
[boundaries](../../../../docs/spec/boundaries.md),
[compiler](../../../../docs/spec/compiler.md),
[relations](../../../../docs/spec/relations.md), and
[endpoint](../../../../docs/spec/endpoints.md) specifications. The public
lifecycle APIs are declared in
[`Artifact.h`](../../../../include/zkc/Artifact/Artifact.h).

### 2.1 More than two graph structures

The sequence and claim graph are primary, but current identified content also
contains:

- material-identity edges from event/result positions to semantic references;
- reduction and round hyperedges spanning claims and transcript occurrences;
- construction routes across values, witness handles, constants, and holes;
- cited semantic-authority closure;
- endpoint coverage relations; and
- policy and segmentation.

Their current co-location is evidence to analyze, not proof that every item
belongs in one future Protocol root.

## 3. Coupled geometry and effect model

### 3.1 Inherent core

The current kernel's decisive invariant is:

```text
ordered transcript and Protocol-effect spine
                  +
linear typed claim and reduction flow
```

PIR maps these onto block order plus a threaded token, and onto SSA claims with
exact-use judgments. Reduction rules refer to both transcript positions and
claim occurrences, so neither can be reconstructed as a mere view of the
other. See
[`PirOps.td`](../../../../include/zkc/Dialect/Pir/PirOps.td) and
[`PirInterfaces.td`](../../../../include/zkc/Dialect/Pir/PirInterfaces.td).

### 3.2 Semantic order versus conservative policy

Every current PIR member writes one `ProtocolResource`, preventing generic CSE,
DCE, speculation, and movement. OIR differentiates endpoint-visible effects
from pure algebra more finely. See
[`OirOps.td`](../../../../include/zkc/Dialect/Oir/OirOps.td).

This suggests a distinction:

- threaded transcript, proof-stream, and explicit events carry semantic order;
- the global PIR resource is a conservative current transformation policy;
- a future observation-indexed effect algebra may admit more precise checked
  independence without weakening whole-Protocol judgments.

Stage 1 must decide whether the blanket resource remains the canonical
semantics, remains workbench defense in depth, or is refined.

## 4. Lifecycle and authority correspondence

The implementation realizes this sequence:

```text
author or importer
  -> Open PIR

Open PIR + ProtocolEnvironment
  -> SealEngine
  -> identified pir.sealed representative

pir.sealed
  -> MLIR bytecode transport
  -> decode + structure + identity authentication
  -> DecodedPirArtifact

DecodedPirArtifact + ProtocolEnvironment
  -> complete seal recheck
  -> AdmittedPirArtifact
```

The division between [`SealEngine`](../../../../lib/Semantics/SealEngine.cpp),
[`Artifact.cpp`](../../../../lib/Artifact/Artifact.cpp), and the private
[`ArtifactInternal.h`](../../../../lib/Artifact/ArtifactInternal.h) supports
several strong invariants:

1. MLIR verification, seal, decode, admission, analysis, projection, and
   execution remain distinct.
2. Serialization does not preserve process-local capability authority.
3. Mutable clones inherit no admission and must be resealed and re-admitted.
4. Cited semantic declarations affect Protocol identity; unrelated environment
   additions need not.
5. Consumers use opaque capabilities or owned facts rather than arbitrary
   mutable operations.

These are architecture-level invariants worth preserving even if the carrier
or dialect structure changes.

## 5. Current MLIR leverage

### 5.1 Already realized

MLIR currently supplies:

- ODS operations, types, builders, accessors, and local verification;
- SSA use-def, dominance, block order, and explicit token structure;
- `IsolatedFromAbove` containers;
- traits and operation interfaces;
- effect resources that protect Protocol and endpoint actions;
- parsing, printing, locations, diagnostics, passes, and textual tests;
- bytecode transport; and
- a strong PIR/OIR level boundary.

This is real value, not merely anticipated reuse.

### 5.2 Mostly custom today

The central semantic algorithms remain zkc-owned C++:

- canonical indexing and encoding use closed case analysis in
  [`CanonicalEncoder.cpp`](../../../../lib/Encoding/CanonicalEncoder.cpp);
- sealing uses the whole-object
  [`SealBattery`](../../../../lib/Semantics/SealBattery.cpp);
- projection constructs OIR through per-operation logic in
  [`PirProject.cpp`](../../../../lib/Dialect/Pir/Transforms/PirProject.cpp);
- admitted compilation uses custom recognition, mutation, resealing,
  readmission, and replay in
  [`PirCompilerProvider.cpp`](../../../../lib/Compiler/PirCompilerProvider.cpp).

The current source does not use generic MLIR dialect conversion as the semantic
authority for PIR-to-OIR and does not yet have a general admitted transform-
validation framework.

**Architecture pressure.** MLIR already earns its place as a structural
workbench. Its largest prospective return—many transforms, synthesis, and
multi-level lowering—is still ahead. Stage 1 should decide whether zkc's center
of gravity is that workbench, an independent semantic boundary, or a deliberate
layering of both.

## 6. Verified architecture correspondence seams

These are statically confirmed relationships that the target architecture must
make coherent. They are not categorized here as bugs.

### 6.1 Protocol identity does not close endpoint/interface behavior

The [`relabel.mlir`](../../../../test/Encoding/relabel.mlir) fixture expects
consistently relabeled PIR artifacts to have the same Protocol ID. The canonical
encoder intentionally normalizes away those authoring labels.

Projection then copies raw instance-bind labels into `statement_labels` and
route witness labels into the prover ABI. OIR's canonical document includes
those labels, and Relations uses statement labels for external wiring. The
soundness adapter also carries some of them in its current broad view.

Consequently:

```text
same ProtocolId
  does not imply same OIR identity
  does not imply one relation-facing interface
  does not make projection a function of only (ProtocolId, endpoint kind)
```

This does not prove that labels belong inside `ProtocolId`. It proves that the
model needs a typed taxonomy and an explicitly identified interface input
wherever erased carrier data affects a normative result.

### 6.2 Sealed PIR is a representative, not a physical normal form

[`SealEngine.cpp`](../../../../lib/Semantics/SealEngine.cpp) computes canonical
bytes and ID, then preserves the authored body rather than rewriting labels and
canonical ordering into one physical form. The encoder performs positional and
ordering normalization internally.

Two `pir.sealed` operations can therefore have different bodies yet the same
canonical bytes and `ProtocolId`.

The accurate current statement is:

> `pir.sealed` is an admitted representative of a canonical semantic
> equivalence class.

Stage 1 must choose whether that remains the design, seal creates a physical
normal form, or a distinct canonical representation is introduced.

### 6.3 Reserved artifact verification exposes an admission-status gap

The kernel says every semantic event derives one projection obligation and
includes `COV_obl` in seal. Current source includes `pir.artifact_verify` in
canonical event numbering and seals its structure, but obligation derivation
has no case for it and projection refuses it earlier. The
[`artifact-verify.mlir`](../../../../test/Encoding/artifact-verify.mlir)
fixture intentionally encodes “seal succeeds, projection refuses.”

That is a coherent reserved-syntax policy, but not the same lifecycle promised
by the current normative seal contract. The ideal model must choose among:

1. reserved authoring syntax cannot enter a sealed executable Protocol;
2. it derives an explicit unsupported or non-executable obligation; or
3. seal has a typed partial result distinct from an endpoint-ready admitted
   Protocol.

### 6.4 Exact canonical grammar has small authority drift

The carrier specification says author labels do not enter PIR canonical
identity but one exact challenge-row grammar lists a label. The implementation
omits it. Because this is an identity grammar, the future documentation model
must assign it one exact authority and maintain a conformance table.

### 6.5 OIR semantic digest description has drifted

The OIR ODS prose says no provenance-independent semantic digest exists, while
the normative carrier and encoder define one. This reinforces that ODS
descriptions should summarize or link, not become a second semantic authority.

## 7. Candidate accidental constraints

The following mechanisms are useful today but must be tested as hypotheses:

1. Open and Sealed PIR use one dialect and nearly the same body schema.
2. One ordered block and a strict phase automaton serve authoring, identity,
   composition, and execution-schedule roles simultaneously.
3. Nonabsorbing events receive a total canonical order partly for deterministic
   identity even when transcript state does not observe that order.
4. One global effect resource prevents expression of finer commutation.
5. Transparent predicates live as inert attribute trees, protecting them from
   generic rewrites but creating a separate algebra inside the dialect.
6. Construction routes and witness declarations enter Protocol identity even
   when multiple prover strategies might share one verifier behavior.
7. Label treatment is mechanism-derived: many event/witness names are erased,
   route-instance names remain, and endpoint labels are identity-bearing.
8. One expanding `SealedSoundnessView` carries facts for several consumers,
   including some not used by current soundness judgments.
9. Operation interfaces make local structure extensible, while canonical
   encoding, obligation derivation, and projection remain closed compiled
   switches.
10. Compiler semantics identifies the complete environment even where a
    provider might eventually declare a smaller exact read set.
11. Projected OIR retains a cloned PIR object for context lifetime, an
    implementation ownership coupling rather than endpoint semantics.
12. MLIR bytecode is the only persisted PIR carrier before an independent
    consumer has justified a narrower portable profile.
13. Immutability is enforced by opaque API ownership over an intrinsically
    mutable IR.

None is rejected by observation alone. Each becomes a candidate comparison or
scenario requirement.

## 8. Native counterexamples

### N1. Equal Protocol ID, different endpoint artifact

Project the two relabeled inputs. Their PIR IDs agree; their statement labels
and therefore OIR identities can differ. This rejects any signature claiming
OIR is determined solely by `(ProtocolId, endpoint kind)`.

### N2. Equal Protocol ID, different relation wiring

Apply label-based relation correspondence to the relabeled representatives.
Protocol identity alone does not determine which external statement interface
is selected.

### N3. Equal identity, different sealed carrier bodies

Seal both relabeled artifacts. Authored labels remain while canonical identity
agrees. This rejects the claim that sealed PIR is already a unique physical
normal form.

### N4. Sealed event without a derived obligation

The reserved artifact-verification fixture seals but has no obligation case.
This pressure-tests whether seal means structurally closed, endpoint-ready, or
a family of typed admission grades.

### N5. Independent nonabsorbing checks

Swap two checks that do not touch transcript state. SSA and Fiat--Shamir state
may agree, while check order, named refusal, and event identity may differ. The
answer depends on protected observers, not purity alone.

### N6. Uncited environment addition

Admission can preserve identity under unrelated additions, while compiler
semantics currently distinguishes the complete environment. This proves that
admission closure and compiler-search read sets are different authority axes.

### N7. One verifier behavior, several prover plans

Vary only witness construction or hole plans while preserving verifier events,
claim graph, and proof ABI. The current representation normally changes
Protocol identity. This tests whether the plan belongs to Protocol, prover OIR,
or a separately identified construction subject.

### N8. Source-free OIR

Persisted OIR can authenticate its own shape and identity, but cannot by itself
reconstruct exact coverage of the source Protocol obligations. This is a
deliberate limit of the endpoint artifact and a pressure for paired projection
evidence when independent checking is required.

### N9. A new event kind

An operation may implement the local Protocol-member interface while still
requiring new compiled cases in canonical indexing, encoding, obligation
derivation, and projection. This distinguishes structural extensibility from
semantic open-world extensibility.

### N10. Same bytes under two regimes

If an intrinsic seal or operation rule changes while the canonical preimage
grammar remains, identical bytes retain their hash but admission can differ.
Long-lived comparison therefore needs an explicit semantic-regime rule.

## 9. Priority questions for candidate evaluation

### Close the subject model first

1. Define semantic ports, external ABI names, dispatch names, author selectors,
   and presentation names.
2. Compare interface inside `ProtocolId`, separate `InterfaceId`, canonical
   positional interface, and explicit carrier-qualified input.
3. Decide whether canonical means normalized physical form, canonical encoding
   quotient, or both.
4. Resolve reserved-event and projection-obligation status.
5. Define semantic-regime scope for admission and cross-version comparison.

### Then choose representation architecture

6. Decide whether authoring and canonical Protocol forms are lifecycle states
   or distinct dialect levels.
7. Place construction routes and prover plans deliberately.
8. Separate semantic dependency, total observable schedule, and incidental
   authored order.
9. Define extension rules separately for canonical event kinds, data-driven
   contracts, authoring extensions, and unknown old-consumer content.
10. Select consumer-specific authenticated views or a shared fact root only
    after exact consumers and trust boundaries are known.
11. Name transform relations and their checking mechanisms per family.

### Finally select external and formal boundaries

12. Assign MLIR a role per level: authoring, canonical representation,
    persistence, endpoint IR, or some subset.
13. Choose independent-checker inputs only after the consumer is concrete.
14. Specify composition and recursion beyond graph union.
15. Define a small formal model and implementation correspondence without
    turning it into an independently evolving compiler IR.

## 10. Candidate-independent invariants supported by the audit

Every serious candidate should preserve:

- a distinct Protocol subject above relation IR and below endpoint realization;
- explicit ordered interactive effects;
- explicit linear claim and reduction flow;
- fail-closed whole-object admission;
- separation of structural admission from property judgments;
- immutable admitted capability boundaries;
- semantic identity independent of generic carrier bytes;
- explicit asymmetric endpoint projection and coverage; and
- checked, identity-aware Protocol transformations.

The audit does not select one versus several dialects, MLIR as a public
portable carrier, Protocol plus Interface or ProverPlan factorization,
physical versus quotient canonicalization, total versus partial-order authoring,
or an independent-checker representation.
