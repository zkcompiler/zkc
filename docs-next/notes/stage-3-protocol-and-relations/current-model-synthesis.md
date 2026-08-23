# Current Protocol, PIR, and Relations model synthesis

> **Document kind:** Temporary Stage 3.1 joint current-model reconstruction
> **Document state:** Complete convergence input; not a design decision
> **Authority:** None. Current normative intent remains in `docs/spec/`, and
> current support remains governed by `docs/status.md`. This synthesis records
> correspondence, conflict, gap, and uncertainty without resolving them.
> **Snapshot:** Repository checkout inspected on 2026-08-22
> **Inputs:** [Current Protocol and PIR reconstruction](current-protocol-pir.md)
> and [Current Relations model and Protocol seams](current-relations-and-seams.md)
> **Scope:** The joint current model across Protocol, canonical PIR,
> Interface-like and Plan-like surfaces, Relations, committed objects,
> Fiat--Shamir, projection, linking, analysis, and verifier descent
> **Non-goals:** This page does not select a Stage 3 candidate, prescribe a
> target architecture, propose migration, or turn tests into semantic or
> security proofs.
> **Disposition:** Route accepted joint findings and conflict boundaries
> through the Stage 3 absorption record to their durable owners; delete this
> note with the completed package before authority cutover.

## 1. Purpose and evidence discipline

The two Stage 3.1 reconstructions examined different faces of the same system.
The Protocol/PIR reconstruction followed the canonical subject from abstract
kernel semantics through carrier, identity, admission, projection, relation
ingress, and linking. The Relations reconstruction followed relation-like facts
from external predicates and artifacts through claim anchors, correspondence,
witness-facing construction, analysis, and composition seams. This document
joins those traces without averaging away disagreements.

Every statement below belongs to one of six evidence classes:

1. **Normative intent** -- an owning specification says what the current model
   means.
2. **Implementation correspondence** -- live code represents or checks some
   part of that intent.
3. **Test correspondence** -- a checked-in or executed test exercises a
   bounded behavior.
4. **Retained history** -- current sources deliberately preserve or reject an
   older representation choice.
5. **Conflict or gap** -- current authorities disagree, or an intended surface
   lacks complete correspondence.
6. **Unknown** -- the inspected current authority does not determine an answer.

The authority rule is the repository's own: an individual specification owns
its named domain, while implementation and test status are separate facts
([`docs/spec/overview.md:3-11`](../../../docs/spec/overview.md#L3-L11)). The
status matrix is explicitly evidence about exact repository examples rather
than universal family compatibility
([`docs/status.md:3-9`](../../../docs/status.md#L3-L9)).

## 2. Joint current architecture

The current architecture is most accurately reconstructed as four connected
but non-isomorphic planes:

```text
external mathematical world
  predicate / relation artifact / public instance / private witness
       |                         no admitted common semantic object
       v
Protocol semantic plane
  total event and transcript spine
  + linear claim/reduction graph
  + opaque claim anchors and material-reference declarations
       |
       | represented, sealed, authenticated, and admitted
       v
canonical carrier and capability plane
  open MLIR PIR -> sealed PIR + ProtocolId -> admitted immutable capability
       |                    |                         |
       | project            | compare post-seal       | analyze / compile
       v                    v                         v
  verifier/prover OIR   RelationContract report   Protocol-claim judgments
       |
       | execute with separately supplied runtime values and suppliers
       v
  bounded run/conformance evidence
```

The center of current semantic authority is the Protocol, not MLIR and not the
RelationContract. MLIR is explicitly a structural carrier
([`docs/spec/carrier.md:13-40`](../../../docs/spec/carrier.md#L13-L40)). A
RelationContract is explicitly post-seal and evidence-only relative to
Protocol identity
([`docs/spec/relations.md:20-46`](../../../docs/spec/relations.md#L20-L46)).
OIR is a derived, separately identified endpoint artifact, while Soundness and
Compiler judgments name exact Protocol claims rather than first-class relation
subjects.

This division is coherent at the opacity boundary: the kernel can precisely
judge an obligation about opaque anchors without pretending to know its
mathematical denotation. It becomes incomplete where current downstream
surfaces read facts that are either erased from `ProtocolId`, embedded in the
wrong subject, or never joined by an admitted relation.

## 3. Current subject and identity inventory

| Subject or concept | Current carrier or representation | Current identity and authority | Exact current limit |
|---|---|---|---|
| Protocol | Semantic tuple represented by one `pir.protocol` / `pir.sealed` body | Canonical positional `ProtocolId`; admitted as an immutable process-local capability | Abstract kernel exceeds the accepted carrier in objects, challenge origins, and decisions. |
| Protocol claim | Profile, exact anchor dictionary, and canonical occurrence | Descriptor digest plus artifact-local `ClaimRef` | Obligation identity, not mathematical relation denotation or satisfaction. |
| Canonical PIR | Closed MLIR grammar and canonical semantic encoder | Carrier bytes are authenticated; `ProtocolId` hashes canonical semantic content | Author labels are quotiented out although some consumers read them. |
| Protocol Interface | No first-class subject | None | Interface facts are dispersed among binds, labels, anchors, routes, OIR, and RelationContract. |
| Prover Plan | No first-class subject | None | Embedded construction routes are the closest analogue and share Protocol identity. |
| Endpoint OIR | Projected verifier or prover program | Separate OIR identity; execution requires accepted endpoint/run authority | Derived operational program, not Protocol or relation truth. |
| Relation definition | No admitted object | None | Mathematical predicate and source relation remain external. |
| RelationContract | Closed post-seal registry entry | Tagged content digest at load; no reusable admitted capability | Interface/evidence declaration, not relation denotation or evaluator. |
| Relation artifact | Optional bytes supplied to the CLI | Optional computed digest; no admitted artifact subject | Only bounded format facts are read. |
| Relation interface | Fields inside RelationContract | Indirectly covered by contract digest | No independent subject, identity, or admission boundary. |
| Relation instance | Encoding declaration plus statement-label map | No typed actual-instance identity | Runtime values are not joined to claim instance anchors by an admitted judgment. |
| Witness interface | RelationContract ports; independently, route witnesses/OIR handles | Covered by different contract and Protocol/OIR identities | No judgment relates the two interfaces. |
| Witness assignment | Runtime handles and supplier inputs | Exact run inputs may be digested | No relation-local ownership, lifetime, or satisfaction semantics. |
| Committed object | Profiled bind/slot plus `ValueProfile` | Profile content cited through ProtocolVocabulary | Opaque size/origin/binding declaration; no committed-content relation semantics. |
| Relation correspondence result | CLI JSON evidence ledger | Normative spec expects identified canonical content; implementation emits no report id | Not admitted or consumed as an immutable premise. |
| Security/compiler result | Judgment over exact Protocol claims or transitions | Identified/capability-bounded in its owning subsystem | Not a general relation or property-transport judgment. |

The Protocol tuple and its two simultaneous geometries are normative:

```text
P = (E, <=, A, C, R, chi, K, anchors, B_M)

event/transcript geometry:  one total ordered spine, with absorbing subset A
claim geometry:             linear sources, reductions, and terminal sinks
```

The tuple is defined at
[`docs/spec/kernel.md:59-97`](../../../docs/spec/kernel.md#L59-L97). Claims are
obligations with exact profiles and anchor dictionaries, not runtime booleans
or proofs
([`docs/spec/kernel.md:180-207`](../../../docs/spec/kernel.md#L180-L207)).

## 4. Current normative intent, joined across domains

### 4.1 Protocol and admission

The intended Protocol is a closed public-coin protocol object whose total
observable schedule fixes transcript order and whose linear claim graph
accounts for every proof obligation. Seal is intended to establish structural
well-formedness, claim linearity, challenge binding, event-obligation coverage,
reduction closure, and terminal closure. Endpoint projection separately
establishes realized coverage
([`docs/spec/kernel.md:731-828`](../../../docs/spec/kernel.md#L731-L828)).

Content-pinned ProtocolVocabulary entries give exact local meaning to claim
profiles, value profiles, checks, holes, reductions, and terminal rules. Opaque
anchors form a membrane: the kernel may compare and bind exact references but
may not infer relation denotation, statement meaning, satisfaction, witness
correctness, or source-compiler correctness
([`docs/spec/kernel.md:319-351`](../../../docs/spec/kernel.md#L319-L351)).

The lifecycle intentionally separates:

```text
open Protocol --seal--> sealed canonical Protocol
sealed bytes --decode/authenticate--> decoded artifact
decoded artifact + exact environment --recheck/admit--> immutable capability
```

Bytes and a matching digest do not themselves confer semantic admission.
The owning boundary contract requires consumers to receive the admitted
capability rather than trust a mutable operation or cached verdict
([`docs/spec/boundaries.md:13-79`](../../../docs/spec/boundaries.md#L13-L79)).

### 4.2 Canonical PIR

The carrier intends one closed, fixed-phase, single-block representation. The
spine operations establish total event position and transcript threading; tail
operations express claims, reductions, material edges, and sinks. Canonical
encoding replaces author selectors with positions and normalizes claim-flow
order, while retaining semantic strings and exact cited content
([`docs/spec/carrier.md:236-263`](../../../docs/spec/carrier.md#L236-L263),
[`docs/spec/carrier.md:308-411`](../../../docs/spec/carrier.md#L308-L411)).

The identity boundary is intentionally semantic rather than textual. Policy,
construction profile, cited vocabulary, events, claims, material bindings,
routes, and segments contribute. Human protocol names, stored ids, evidence,
backend names, and derived judgments do not
([`docs/spec/kernel.md:830-896`](../../../docs/spec/kernel.md#L830-L896)).

### 4.3 Interface-like intent

No current specification declares a `ProtocolInterface` subject. Instead, the
intended external face is distributed:

- claim profiles define anchor shape;
- instance-stage binds define ordered public inputs;
- author labels become OIR statement labels;
- routed sinks expose named claim exits;
- material references expose stable semantic attachments;
- RelationContract maps public relation positions to statement labels; and
- OIR authenticates its public entry signature and labels.

These mechanisms express useful individual facts, but no current normative
relation says that one identified interface is the complete external face of a
particular Protocol. The endpoint ABI is specified at
[`docs/spec/endpoints.md:53-76`](../../../docs/spec/endpoints.md#L53-L76), and
the relation statement map at
[`docs/spec/relations.md:179-221`](../../../docs/spec/relations.md#L179-L221).

### 4.4 Plan-like intent

No current specification declares a `ProverPlan` subject. Optional construction
routes embedded in PIR declare route witnesses, content-pinned HoleContract
instances, typed dependencies, and proof-slot sources. They describe how a
prover skeleton may obtain slot values, but neither select executable suppliers
nor prove their algebra
([`docs/spec/vocabularies.md:424-454`](../../../docs/spec/vocabularies.md#L424-L454)).

Missing routes are compatible with seal, while prover projection requires route
totality
([`docs/spec/carrier.md:222-235`](../../../docs/spec/carrier.md#L222-L235)).
Compiler plans and Soundness derivation plans are separate consumer concepts;
neither is a prover construction plan.

### 4.5 Relations

The normative relation domain keeps `RelationContract` outside Protocol
identity. Its closed schema pins a claim profile, partitions relation and
instance anchors, declares a format and identity evidence, describes public
instance encoding and private witness ports, maps relation statement positions
to artifact labels, and may declare bounded shape
([`docs/spec/relations.md:55-68`](../../../docs/spec/relations.md#L55-L68)).

Its correspondence judgment compares one sealed artifact, one contract, and
optional bytes. Evidence is classified as computed, cross-checked, or asserted.
Cross-check agreement means consistency, not truth. Intended predicate meaning,
absence of underconstraint, witness-generator correctness, slot meaning,
provenance, and bytes-to-anchor correspondence remain explicit nonclaims
([`docs/spec/relations.md:269-306`](../../../docs/spec/relations.md#L269-L306),
[`docs/spec/relations.md:377-388`](../../../docs/spec/relations.md#L377-L388)).

The current model therefore intends relation correspondence to be narrower
than all of the following:

```text
relation definition
relation artifact admission
typed relation-instance construction
witness assignment or capability
RelationSatisfies(instance, witness)
proof of relation meaning or compiler correctness
```

### 4.6 Fiat--Shamir and property analysis

The current kernel gives the same Protocol spine an interactive fresh-sampling
reading and a construction-profile duplex-sponge reading. There are no
separately identified fresh and Fiat--Shamir Protocol subjects and no current
`FSCompile` relation. The construction profile pins sponge and codec facts, but
backend transcript conformance and the Binding Lemma remain separate
obligations
([`docs/spec/kernel.md:78-97`](../../../docs/spec/kernel.md#L78-L97),
[`docs/spec/kernel.md:927-966`](../../../docs/spec/kernel.md#L927-L966)).

The implemented Soundness bridge transports one StateRestoration scalar result
to one FiatShamir scalar result while adding construction-specific terms. It is
a property-specific judgment about the same Protocol claim, not a construction
of a second Protocol, an event map, or a general property transport
([`docs/spec/soundness.md:875-913`](../../../docs/spec/soundness.md#L875-L913)).

### 4.7 Linking and composition

The normative `link` boundary consumes two open Protocols, fuses exact
export/source faces, namespaces and splices schedules, composes routes,
preserves material references, rechecks the resulting Protocol, and records
challenge/seam composition obligations
([`docs/spec/boundaries.md:279-334`](../../../docs/spec/boundaries.md#L279-L334)).

This is authoring-time Protocol construction. It is distinct from:

- composition of RelationContracts, relation instances, or witnesses;
- aggregation of already admitted child Protocol capabilities;
- verifier-as-relation descent;
- a theorem that soundness, completeness, or zero knowledge composes; and
- a general property-transport relation.

Verifier descent is a reserved direction from an executable verifier face to a
relation payload, with explicit child identity, ABI, assumption, and
self-reference obligations
([`docs/spec/kernel.md:1037-1084`](../../../docs/spec/kernel.md#L1037-L1084)).

## 5. Implementation and test correspondence

### 5.1 Strong current correspondence

The following parts have direct implementation support in the inspected
checkout:

- closed TableGen/MLIR PIR grammar and two-pass container verification;
- exact one-use claim linearity;
- fresh-challenge binding checks with contract-derived prefix requirements;
- content-driven reduction and terminal closure for admitted current contracts;
- positional canonical encoding and tagged SHA-256 Protocol identity;
- decode, identity authentication, exact-environment recheck, and immutable
  admitted capability;
- verifier and prover OIR projection for the supported event vocabulary with
  exact source-position coverage;
- construction-route parsing, typing, acyclicity, temporal availability, handle
  linearity, and prover-route totality;
- closed RelationContract loading and tagged contract digest;
- optional relation-byte hashing and bounded R1CS header reading;
- post-seal computed/cross-checked/asserted relation reporting; and
- fresh/local open-PIR linking with exact claim-face fusion, namespace
  rewriting, schedule concatenation, material preservation, route composition,
  and composite rejudgment.

Representative implementation anchors are
[`lib/Semantics/SealEngine.cpp:144-229`](../../../lib/Semantics/SealEngine.cpp#L144-L229),
[`lib/Encoding/CanonicalEncoder.cpp:1456-1478`](../../../lib/Encoding/CanonicalEncoder.cpp#L1456-L1478),
[`lib/Dialect/Pir/Transforms/PirProject.cpp:280-344`](../../../lib/Dialect/Pir/Transforms/PirProject.cpp#L280-L344),
[`lib/Semantics/ConstructionGraph.cpp:208-554`](../../../lib/Semantics/ConstructionGraph.cpp#L208-L554),
[`lib/Registry/RelationContractRegistry.cpp:125-455`](../../../lib/Registry/RelationContractRegistry.cpp#L125-L455),
and
[`lib/Semantics/LinkEngine.cpp:231-422`](../../../lib/Semantics/LinkEngine.cpp#L231-L422).

### 5.2 Bounded test evidence

The Protocol/PIR reconstruction inspected the checked-in carrier, sealing,
closure, encoding, projection, link, and relation tests but did not execute
them. Their source asserts exact bounded behaviors; it is not a new passing
result. The Relations reconstruction executed the current relation unit-test
binary and observed `13 cases, 0 failed`, covering anchor projection and the
bounded R1CS header reader only. Its selected lit runs could not create the
sandbox multiprocessing socket, so no fresh lit pass claim was made.

The most important source-declared boundaries are preserved by:

- [`test/Encoding/relabel.mlir`](../../../test/Encoding/relabel.mlir), which
  asserts `ProtocolId` stability under consistent author-label renaming;
- [`test/Encoding/artifact-verify.mlir`](../../../test/Encoding/artifact-verify.mlir),
  which asserts canonical seal/encoding but projection refusal for the bounded
  child-verification row;
- [`test/Transforms/pir-link.mlir`](../../../test/Transforms/pir-link.mlir),
  which asserts fresh/local splice behavior while disclaiming an FS seam
  soundness claim;
- [`test/Relation/relation-contract.test`](../../../test/Relation/relation-contract.test),
  which exercises current relation registry/report behavior; and
- [`test/Relation/relation-disagreements.test`](../../../test/Relation/relation-disagreements.test),
  which deliberately treats a disagreement as a negative judgment rather than
  inability to reach a subject.

### 5.3 Partial or absent correspondence

The accepted carrier is narrower than the abstract kernel: it has fresh
challenges only, flat profiled values rather than general stateful objects, and
no source Protocol decision event. Seal-policy enforcement currently covers
only permitted sink kinds. `artifact_verify` has an identity-bearing carrier
row but no projection, execution, or complete obligation semantics. Relation
reading stops at interface/header facts. Neither Interface nor Plan has a
standalone identity/admission boundary. The current status matrix also labels
these families partial or reserved
([`docs/status.md:93-119`](../../../docs/status.md#L93-L119)).

## 6. End-to-end seam trace

The following trace shows what is joined today and where semantic continuity
ends.

| Stage | Current input and output | Fact established | Continuity that is not established |
|---|---|---|---|
| Relation-flavored claim ingress | `pir.instantiate(profile, anchors) -> Claim` | Exact admitted profile/anchor shape and claim occurrence | Which mathematical relation the anchors denote |
| Public statement ingress | Instance-stage binds in total Protocol schedule | Ordered, typed, transcript-visible public values | Typed `RelationInstance` and equality to its instance anchor |
| Witness declaration | RelationContract witness ports | Declared private interface shape | Equality to route witnesses, OIR handles, or a concrete assignment |
| Prover construction | Embedded PIR routes -> prover OIR skeleton | Typed, acyclic, temporally valid source graph; totality at prover projection | Supplier algebra, witness correctness, or relation satisfaction |
| Committed values | `ValueProfile` plus profiled bind/slot | Declared class, arity, origin, and binding route | Opening/content truth or relation-local object meaning |
| Seal and admission | Open PIR -> sealed bytes -> admitted capability | Current structural Protocol judgments and exact-environment authority | Relation meaning or relation artifact admission |
| Interface projection | Admitted PIR -> OIR | Supported event lowering, endpoint ABI, exact realized coverage | Projection as a function of `ProtocolId` alone when erased labels are read |
| Relation correspondence | Artifact presentation + RelationContract + optional bytes -> report | Bounded consistency ledger and named residual assumptions | Stable exact subject, typed invocation, satisfaction, or report admission |
| Fiat--Shamir analysis | Protocol claim result + construction facts -> FS result | One property-specific conditional bound transformation | Distinct source/target Protocols or general property transport |
| Static link | Two open PIRs -> one rejudged open PIR | Fresh/local structural splice and exact claim/material/route rewriting | Relation composition, seam theorem, or security composition |
| Verifier descent | Reserved `SealedP -> RelationPayload'` direction | Requirements only | Executable child verification, relation satisfaction, recursion, or composition |

The key joint observation is not simply that some features are missing. The
existing seams use different subjects:

- claim and transcript facts are authenticated by `ProtocolId`;
- endpoint labels and ABI are authenticated by OIR identity;
- relation interface declarations are authenticated by RelationContract
  digest;
- route witnesses are embedded in Protocol identity;
- actual suppliers and inputs are bound only by execution/run evidence; and
- current analysis conclusions name Protocol claims.

No present admitted object records the exact relation among all of those
subjects.

## 7. Compact cross-domain conflict and gap table

| ID | Domains crossed | Classification | Current observation | Why it matters to the baseline |
|---|---|---|---|---|
| X-01 | PIR identity / OIR / Relations | **Direct conflict** | `ProtocolId` erases author labels, but projection and relation correspondence read those labels and can produce different identified/output behavior for id-equivalent presentations. | Current downstream behavior is not determined by the subject identities it names. |
| X-02 | Relations spec / relation CLI | **Direct conflict** | The spec says failed content/field comparisons refuse; code and tests emit a negative report with exit 1. | The current outcome algebra is not singular. |
| X-03 | Relation anchor semantics / CLI grounding | **Direct conflict** | The spec gives relation anchors transcript-projection grounding and instance anchors statement-wiring grounding; the CLI also applies statement wiring to relation anchors. | The two anchor partitions are operationally conflated. |
| X-04 | Relations / Soundness FS accounting | **Direct conflict** | Relation correspondence treats all declared relation anchors as candidates for transcript carriage; Soundness counts only an anchor literally named `contract`. | The same current artifact can have inconsistent relation-binding scope across domains. |
| X-05 | Normative opacity / live vocabulary | **Direct conflict** | Current documents make RelationContract evidence-only and `opaque_relation` anchors uninterpreted, while the live `relation-direct` predicate demands a RelationContract decision entrypoint and witness source that the closed schema cannot contain. | The live predicate cannot execute under the current admitted model. |
| X-06 | Relations identity / CLI selection | **Direct conflict** | The spec says judgments consume contract digests and do not resolve by name; the CLI requires a registry key lookup. | Invocation authority is wider than the emitted subject. |
| X-07 | Carrier vocabulary / bounded child row | **Direct conflict** | Vocabulary prose calls `artifact_verify` reserved with no accepted representation, while carrier, encoder, seal path, tests, and status admit a canonical but non-projectable row. | “Reserved” has two incompatible current meanings. |
| X-08 | Carrier / downstream subject | **Gap** | Relation report emits artifact id and contract digest but omits matched `ClaimRef`, report id, relevant input identities, and admission path. | The result is occurrence-ambiguous and not replayable as a durable premise. |
| X-09 | Relations / endpoint construction | **Gap** | RelationContract witness ports are never related to route witnesses, OIR handles, suppliers, or invocation inputs. | A declared witness interface does not identify an actual witness subject. |
| X-10 | Instance anchors / runtime ABI | **Gap** | Statement labels, header arity, and declarations are checked, but no typed actual instance is constructed and bound to the claim's instance anchor. | Correspondence remains interface consistency rather than invocation correspondence. |
| X-11 | Committed objects / Relations | **Gap** | ValueProfile facts and `instance_encoding = commitment` have no admitted connecting relation. | Commitment-shaped instances remain declarations without content semantics. |
| X-12 | Abstract Protocol / PIR | **Gap** | General object state, projected/derived/imported challenges, and Protocol decision events exceed the current carrier. | Abstract intent cannot be read as implemented carrier semantics. |
| X-13 | Seal / projection coverage | **Gap** | `artifact_verify` is canonically indexed but has no derived seal obligation or projection discharge. | Current seal does not realize the normative one-obligation-per-event story for that row. |
| X-14 | Link / FS / Relations | **Gap** | Implemented link covers fresh/local structural splice, but does not materialize seam obligations, imported challenges, relation maps, or property composition. | Static linking is narrower than general semantic or theorem composition. |
| X-15 | Interface / Plan authority | **Gap** | Interface-like facts are dispersed and Plan-like routes are embedded in Protocol identity; neither has its own identified capability. | Current ownership cannot express independent variation or exact cross-subject relations. |
| X-16 | Canonical docs / implementation domains | **Direct documentation conflict** | Carrier challenge-row prose includes an author label that the positional encoder omits; the “exhaustive” domain list omits live value-profile and relation-contract domains. | Current canonical-identity prose is not internally literal without correction. |

Additional local conflicts and source anchors remain catalogued in the two
input reconstructions. This table contains only conflicts and gaps that affect
the joined Protocol/PIR/Relations model.

## 8. Retained history and deliberate clean breaks

The current shape is partly explained by explicit historical decisions. These
facts constrain reconstruction of what exists; they do not become requirements
for later design.

- Canonical encoding deliberately removed reduction theorem citations,
  container hop citations, and sealed theorem rows. Older encodings are not
  treated as loader migration inputs
  ([`docs/spec/carrier.md:445-450`](../../../docs/spec/carrier.md#L445-L450)).
- The former `chal` pseudo-payload class was retired so that challenge origin
  and semantic payload class remain orthogonal
  ([`docs/spec/vocabularies.md:235-241`](../../../docs/spec/vocabularies.md#L235-L241)).
- `opaque_relation` remains as a small compatibility-shaped profile after
  relation interpretation moved to the external contract boundary.
- Scalar carrier and OIR rows are intentionally retained while vector,
  profile, route, and segment information is added under distinct row heads or
  optional tails.
- V0 promises exact content identity, not schema compatibility, legacy
  decoding, or artifact upgrades
  ([`docs/spec/versioning.md:3-13`](../../../docs/spec/versioning.md#L3-L13)).
- RelationContract was intentionally excluded from `ProtocolEnvironment` and
  ProtocolVocabulary so post-seal evidence cannot silently change Protocol
  identity. A checked-in registry test preserves rejection of an ambient
  `relation_contracts` vocabulary section
  ([`test/Registry/protocol-vocabulary.test:36-42`](../../../test/Registry/protocol-vocabulary.test#L36-L42)).

These choices explain why exact Protocol structure is relatively mature while
relation meaning and external interface authority remain deliberately outside
the seal.

## 9. Unknowns preserved for later research

Current authority does not settle the following questions:

1. What identifies a mathematical relation independently of source text,
   artifact bytes, RelationContract documents, and Protocol anchor tuples?
2. What are the exact subjects of relation definition, relation interface,
   actual instance, witness interface, witness assignment, and invocation?
3. When do two relation artifacts, contracts, or interfaces denote equality,
   refinement, translation, or unrelated meanings?
4. Which authenticated object owns the complete public/proof/decision ABI of a
   Protocol, and how is it related to canonical Protocol identity?
5. Which prover-construction facts belong to Protocol meaning, independent plan
   identity, endpoint realization, or runtime supplier selection?
6. Who may create, delegate, consume, retain, or destroy a private witness
   capability, and which of those facts may be globally identified?
7. Which judgment constructs an actual typed relation instance from runtime
   inputs and binds it to Protocol claim anchors?
8. Which judgment may decide or evidence relation satisfaction, with what
   evaluator authority, outcome algebra, and residual trust?
9. How is a correspondence result exactly identified, authenticated, admitted,
   replayed, invalidated, and consumed?
10. Is Fiat--Shamir only a second reading of one Protocol or an explicit
    source-to-target construction, and what maps challenge occurrences and
    transcript prefixes?
11. Which properties transport across which relation, Protocol construction,
    compiler transformation, or composition relation, under which theorem or
    model basis?
12. How do link/composition combine public instances, private witnesses,
    relation refinements, shared or imported challenges, domains, failures, and
    child-to-composite occurrence maps?
13. What exact semantics lets verifier descent expose a child verifier as a
    relation without widening its ABI, claims, assumptions, or acceptance
    meaning?
14. Whether re-admission is intended to be self-contained from artifact-pinned
    preimages or to require the current external `ProtocolEnvironment` remains
    unclear
    ([`docs/spec/kernel.md:889-896`](../../../docs/spec/kernel.md#L889-L896)).

These are semantic unknowns, not implementation TODOs inferred from preferred
architecture. Stage 3 alternatives must answer or explicitly defer them.

## 10. Strongest supported current envelope

The strongest joint statement supported by current normative intent,
implementation correspondence, and bounded evidence is:

> zkc currently defines and implements a substantial closed Protocol core: one
> totally scheduled public-coin transcript spine, one linear content-pinned
> claim/reduction graph, exact checks and terminals, opaque semantic anchors,
> flat committed-value profiles, optional typed construction routes, and
> canonical positional identity carried in MLIR PIR. It can seal,
> authenticate, recheck, and immutably admit the supported artifact; project
> supported verifier and prover OIR with exact event coverage; structurally
> link a bounded fresh/local open-PIR subset; and produce bounded post-seal
> evidence about consistency between an artifact presentation, a
> RelationContract, and optional relation bytes.

That envelope does **not** support claims of:

- a first-class relation definition, relation interface, actual relation
  instance, witness assignment/capability, or satisfaction judgment;
- one identified Protocol Interface or independently identified Prover Plan;
- correspondence as a stable function of the identities currently emitted;
- general object-state semantics or non-fresh challenge origins in PIR;
- separately identified fresh and Fiat--Shamir Protocols or a structural
  `FSCompile` relation;
- general property transport or security composition;
- relation-aware Protocol composition, child verification, recursion, or
  verifier-as-relation descent;
- complete enforcement of every normative policy and coverage dimension;
- relation bytes denoting sealed anchors, witness-generator correctness,
  non-underconstraint, or source-compiler correctness; or
- formal proof that current code implements the full abstract kernel.

## 11. Stage 3.1 joint conclusion

The current model has a strong and coherent structural nucleus: exact Protocol
events, transcript order, linear claim flow, content-pinned local contracts,
canonical semantic identity, and immutable consumer admission. The kernel's
opaque-anchor boundary also correctly prevents structural success from being
misreported as relation truth.

Around that nucleus, the external face is fragmented. Public interface facts
are split across identity-erased PIR labels, identity-bearing OIR ABI, claim
anchors, routes, and RelationContract maps. Prover construction is embedded in
Protocol content but is not a supplier or correctness subject. Relations can
record useful post-seal consistency evidence but cannot yet identify actual
instances or witnesses, establish satisfaction, or become an admitted premise.
Fiat--Shamir is a second reading and a property-specific analysis bridge rather
than an explicit Protocol construction. Link is a bounded open-authoring
splice, not a general relation or property composition operator.

Those boundaries are the complete Stage 3.1 baseline. Later research may
preserve, refine, or replace any of them, but it must account for the retained
strengths, the direct conflicts in Section 7, the explicit nonclaims, and the
unknowns in Section 9. This synthesis makes no target selection.
