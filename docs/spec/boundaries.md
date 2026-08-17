# zkc Boundaries

Status: **canonical for the PIR/OIR boundaries.** Companion to
`kernel.md`: three admitted checked boundaries,
the reserved `descend` research signature, and the reserved backend-realization
contract. No new protocol semantics is defined here; a rule that cannot be
derived from a kernel judgment plus an admitted vocabulary entry is a spec
bug. OIR endpoint-program semantics live in `endpoints.md`.

This document is canonical for the PIR carrier boundaries. The
post-seal `soundness.md` calculus is the derivation boundary and the only
place a conditional security statement is produced: the artifact denotes
structure, and no pricing or certificate surface stands between the seal and
that calculus.

## 0. Consumer and assurance contract

**The consumer contract** (kernel §0): a boundary receiving raw Open PIR
verifies its structural representation and the judgments named by that
boundary. A boundary receiving a raw identified PIR or OIR artifact also
recomputes its identity. An operation may instead require an opaque
authenticated capability that unforgeably binds an immutable subject or closed
derived view to its identity and the authority used at admission. Caller
assertions, cached booleans, receipts, and mutable handles do not substitute for
authentication. A derivation remains bound to the exact immutable subject it
authenticated, so it cannot be cross-wired to another artifact or reused after
mutation. Purpose-specific judgments and endpoint execution under the declared
ABI remain the responsibility of their consuming boundary. Raw
identity-minting translations are the deliberate exception: they author an id
and confer no acceptance. Arbitrary hostile target contexts are out of scope by
design.

**Assurance methodology, named precisely.** Differential agreement between
two implementations of this specification is evidence against implementation
error, not semantic authority. Any such conformance claim MUST identify the
exact judgments compared, the accepted and rejected corpora, and every excluded
dimension. It remains subject to the Knight–Leveson common-mode caveat: both
implementations may misread the same specification in the same way. The term
"translation validation" is reserved for Tier 4 (§5), in its literature sense.

Agreement on accepted inputs is insufficient. Conformance evidence MUST also
exercise semantic refusals, because identical bytes can be produced without
either implementation enforcing the meaning of every field. Numeric bound
composition additionally requires independent source re-derivation or formal
justification; byte or verdict parity alone cannot establish the cited
cryptographic calculation.

```text
seal    : OpenP × Envs                       → Option⟨SealedP⟩
decode  : Artifact                       → Option⟨DecodedSealedP⟩
admit   : DecodedSealedP × Envs              → Option⟨AdmittedSealedP⟩
project : AdmittedSealedP × endpoint_kind    → Option⟨OIRArtifact⟩
link    : OpenP × OpenP × faces × Envs       → Option⟨OpenP⟩
descend : SealedP (realized verifier)         → RelationPayload'
          (reserved research signature; unsupported)
oir-realize : OIRArtifact × ProjectionContext × target
              → backend artifact + evidence
              (reserved; out of scope for this revision)
```

Here `Envs` is the `ProtocolVocabulary` and construction-profile
environment supplied to the operation. Each operation uses one environment
consistently for every vocabulary-dependent judgment it performs.

All boundaries are fail-closed: failure produces diagnostics only,
never a partial semantic artifact. Diagnostic ids are stable and per-axis;
concrete ids are a carrier concern.

PIR admits `seal`, `project`, and `link` as checked boundaries. `descend` and
`oir-realize` are reserved contracts, not callable boundaries of this format.

## 1. seal

Signature as above. `OpenP` carries its selected construction profile and SealPolicy.
Anchor values are opaque digest-shaped
semantic references carried by the artifact; seal does not load or validate a
`RelationContract` (`relations.md`) or `BindingSchema` body. That separation
is an intentional boundary, not a missing seal check: the contract is
post-seal by design.

The check battery is exactly the kernel conjunction:
WF/LIN/BIND/COV_obl, `TerminalClosureOK`, and `ReductionClosureOK`. The two
closure judgments prevent terminal selection and reduction semantics from
remaining shape-only carrier assertions:

- **WF** — exact claim-profile/anchor agreement; check-contract parameter,
  semantic-role, mode, operand-class, and unique-segmentation agreement;
  joint ProtocolVocabulary admission, including re-derived
  predicate-spec content keys, exact cited preimage closure, entrypoint
  resolution, and structural ABI equality for every opaque CheckContract;
  construction-route shape, reference, anchor, class, count, parameter, and
  acyclicity checks, including exact resolution of every cited HoleContract
  under its content digest;
  canonical `ValueRef`/`MaterialRef` binding shape and reverse-injectivity;
  cross-admitted protocol-vocabulary resolution; encodability;
  origin well-foundedness, and body disjointness.
- **LIN** — root claims from valid sources; descriptor
  anchors exact against the selected claim profile (for
  source and reduce-produced claims alike) and digest-shaped
  (zkc-E156); single production/consumption; explicit multiplicity;
  sinks permitted by policy;
  carrier-transfer reductions traceable. (claim checks 1–6.)
- **ReductionClosureOK** — every reduction resolves one exact
  `ReductionContract`; its consumed profiles, dependency/message/round shape,
  parameter sorts, and output profiles match; its exact role map selects all
  and only the contract-owned checks; pinned check contracts, parameters,
  transparent predicates, attachments, and ownership agree; material
  constraints evaluate; and the contract independently reconstructs every
  authored output anchor. Missing or extra checks, arbitrary static parameters,
  unresolved material, or output drift refuses (kernel §4.1).
- **TerminalClosureOK** — every discharge resolves one check-backed terminal
  rule, matches the exact consumed descriptor and optional producer pattern,
  binds exactly and injectively the rule roles to matching check contracts,
  proves complete claim/check attachment coverage, matches every transparent
  check expression to the rule's normalized predicate, and resolves every
  material equality through the exact
  `MaterialBinding`. Every binding is consumed; a selected check belongs to at
  most one discharge. Unknown, stale, missing, extra, ambiguous, crossed, or
  unproved-alias content refuses (kernel §4.2). A terminal rule may reuse a
  selected check only from the exact matched producer contract/output; every
  other cross-owner reuse refuses.
- **BIND** — fresh challenges after their required prefix, where the
  requirement set of a contract-owned challenge is **generated from the
  reduction contract's declared round structure** (kernel §5.2 — hand entries
  extend, never replace); the two structural defaults (unabsorbed
  slots after the last challenge; every public_bind before the first
  challenge — kernel §5.3) unless a cited relaxation row applies;
  origin and semantic payload class kept distinct; exact payload class,
  domain, space, count, sampling rule, and exclusive-use satisfaction;
  projection/derivation
  provenance; no backend-substituted schedules; **imported challenges
  become composition obligations** (kernel §5.4) — recorded, and
  fatal under closed-proof policy. (challenge checks 1–6, effect
  checks 1–3, plus the PIR generation and statement rules.)
- **COV_obl** — every semantic event derives one projection
  obligation under the closed route/discharge vocabulary (kernel
  §6.1): `executable` derived by default, non-executable classes only
  by declaration with route refs (declaration surfaces are a named
  extension; PIR encodes no such declaration surface); unknown vocabulary
  fails closed. The
  codec-coverage checks (zkc-E221) belong here semantically —
  deriving a bind/slot/challenge obligation consumes the payload
  class's codec — even though the carrier reports them on the
  WF-profile axis (a reporting fact, not a judgment move).
  Realization is not sealed: COV_realized is proved per endpoint at
  pir-project (§2). (projection
  checks 1–4; effect checks 4–6 fold into event/route validity.)
- **Policy and evidence** — ZK release policy (membrane), assumption
  visibility, residual/export ownership
  generation, profile fields do not alter semantics. (security checks
  1–5.)

Products: the sealed artifact; tabulations of E, χ, C, K (views —
kernel §11); the projection obligation table; composition obligation
rows; one reconstructible reduction-closure row per reduction; and one
reconstructible terminal-closure row per discharge. These closure rows are
seal-internal evidence; a security statement about the artifact is a separate
post-seal derivation (`soundness.md`). Identity per kernel §8.

For opaque checks these products establish **predicate identity**, not
**predicate execution**. The admitted CheckContract digest pins one exact
predicate-spec content digest, entrypoint, and structural ABI, and any
consumer re-admitting the artifact re-derives exactly that cited preimage
closure. Neither seal nor consumer-side re-admission invokes an adapter,
decides the predicate on runtime values, proves adapter conformance, resolves
a relation payload or SRS, or upgrades the proposition's acceptance text into
a theorem. OIR therefore carries the contract digest as dispatch authority
while execution and conformance remain separately attributable evidence
facets.

## 2. project

Input: an opaque admitted sealed-artifact capability and an endpoint kind.
Output: one
`OIRArtifact` (never a naked program):

```text
OIRArtifact {
  id, source_pir_artifact_id, endpoint_kind,
  program            — the Fiat-Shamir handler image; every operation that
                       realizes a source obligation carries `src`, the
                       canonical event positions it covers
}
```

The capability binds one immutable decoded subject to the exact environment
used for admission. Decode authenticates the transport, structure, and
canonical PIR identity; admission then rechecks the complete seal judgment
against that environment. Project consumes this authority without repeating
either judgment and clones the subject privately for endpoint construction.
The raw `pir-project` pass is a development adapter: it snapshots and admits
each textual sealed input once before running the same projection engine. It is
not the persisted production boundary.

The carrier follows the views principle: `endpoint_abi` is the program
signature; `route_map` derives from the source artifact's sinks;
`conformance_requirements` derives from policy and endpoint kind; and the
`ProjectionMap` is the tabulation of embedded `src` provenance. The
provenance-independent `semantic_id` is a computable view of the endpoint
semantics and is deliberately not stored. Projection evidence remains embedded
in the operations rather than in a sidecar, so no pass can drop it silently and
there is no mirror to drift.
Rules:

1. **Totality.** For `verifier` and `prover_skeleton` endpoints over a
   public-coin sealed
   artifact that satisfies COV_obl and whose obligations' discharge
   kinds lie in the endpoint's realization vocabulary, projection is
   total: every semantic
   event projects, routes, or the projection fails — there is no
   silent drop; an obligation outside the realization vocabulary is a
   named refusal (`unsupported`), never a partial artifact (kernel
   §10).
2. **Realization equality — COV_realized (kernel §6.2).** The emitted
   program's coverage equals the obligation set exactly, in both
   directions: every executable obligation's event position is
   covered by ops of the families its discharge kind requires, and
   every position appearing in any op's `src` is a real canonical
   event position carried by a family its obligation licenses —
   `src` is the Tier-1 conformance evidence, so its **contents** are
   validated at the boundary that produces them, never only counted
   (a fused op may carry several positions only under a cited fusion
   rule; the v0 fusion set is empty). Non-executable obligations
   route to the artifact's route attribute by ref
   (residual/assumption/export/analysis_only, with route refs —
   vacuous in v0, where none can be declared). Equality is checked at
   project time and by conformance
   tooling holding both artifacts; the artifact alone carries the
   claim (Tier 1 needs both, §5).

   Coverage reports on two axes. Artifact axis:
   `projection_obligations: complete` — true of any sealed artifact
   by construction (seal is COV_obl; the failing form,
   `reject(<diagnostic>)`, appears in failure reports only, since no
   sealed artifact exists in that case). Per-endpoint axis:
   `projection_coverage: realized | unsupported(<discharge kinds>) |
   not_attempted` — `realized` carries the OIR artifact id and its
   `src` tabulation as the witness; `unsupported` lists the
   unrealizable obligations (event positions and discharge kinds)
   when the endpoint's realization vocabulary lacks a discharge kind.
   Scalar and bounded-vector challenges both realize as one counted OIR v3
   squeeze. Raw malformed input is rejected during decode or admission;
   zkc-E233 and zkc-E237 remain projection backstops for an extension or
   implementation mismatch, not capability gaps. `not_attempted` is the
   default when no projection ran — never inherited from seal. The
   empty-verifier-face refusal
   (zkc-E234) is a non-vacuity reject deliberately **outside** the
   coverage verdict: a fully covered program with no check is exactly
   what that rule exists to refuse, and folding it into coverage
   would let "all events realized" read as strength.
3. **RouteMap.** Claim terminal routes and composition obligations
   are cited by id — OIR carries routes as references, never as
   runtime values. The claim graph itself — sources, reduces, sinks —
   emits no program ops: a reduce's executable content is already on
   the spine (its round obligations are check events, its deps are
   squeezed challenges, both priced at seal), so the graph projects
   to views and citations only.
4. **Protocol effects are protected.** Ordered absorb/squeeze/read/
   bind/verify/decide events in the endpoint program are not
   reorderable helper computation; the spine order is the conformance
   target. Projection correctness **factors** (kernel §10): the
   operational correspondence — endpoint event log complete and sound
   against the sealed spine — is the Tier-2 theorem; the security of
   instantiating challenges by hashing is the Binding Lemma, priced
   separately. Conformance evidence for the first half is never
   evidence for the second.
5. **Fail-closed axes.** Unknown endpoint kind, codec, sampling rule,
   sponge, iv policy, or check-lowering vocabulary is a per-axis
   error. An empty declared verifier face is refused (an accept-all
   verifier is unrepresentable). Backend target/profile names do not
   participate at this boundary.
6. **Prover specialization.** `prover_skeleton` projection consumes the same
   obligations but realizes the dual endpoint vocabulary defined in
   `endpoints.md` §6. It requires construction-route totality, uses the
   HoleContract schemas bound by artifact admission, and validates
   verifier/prover lockstep and counterparty rows. These are projection facts,
   not backend-fill or witness-correctness claims.

## 3. link

Composition of open protocols (producer, consumer):

The vocabulary-dependent closure and construction-route checks below use the
single `Envs` argument in the boundary signature.

1. spine splice with operand-prefixed namespaces; label collisions
   are errors; the composite records its **segment decomposition**
   (the operands' segments, concatenated — identity-bearing, kernel
   §5.3): the statement-binding default is judged per segment over
   the composite, the Frozen-Heart default globally;
2. the consumer's declared producer face is checked structurally;
3. behavioral profiles merge axis-wise; conflicts are ill-typed;
4. claim flows compose: exported/deferred claims of the producer may
   be consumed by the consumer's declared sources — LIN is re-judged
   over the composite;
5. **composition obligations discharge here**: imported-challenge
   BIND requirements are re-checked by precedence-plus-absorption
   over the composed spine (kernel §5.4). Obligations that remain
   unresolved survive as composition-obligation rows, fatal at any
   later closed-proof seal;
6. **joint transcript state is re-separated** (kernel §5.4):
   challenge domains are re-derived under the link faces' prefixes
   (aggregation of already sealed children instead uses child identities as
   namespaces), and domain disjointness is re-judged over the
   composite — two separately sealed, separately BIND-clean
   artifacts may still collide in domains or share a sponge once
   composed;
7. one `fs_segment_seam` obligation per splice is recorded on the
   composite (artifact-scope, beside `binding_lemma`) and is
   discharged only by a post-seal derivation whose plan covers the
   seam — stated, never implied (kernel §5.3);
8. `MaterialRef` targets are preserved byte-for-byte. Every local `ValueRef`
   endpoint is rewritten to the corresponding composite event/result port.
   The merged binding set must remain a partial function and reverse-injective;
   equal material targets from distinct surviving producers refuse. Link may
   collapse them only when its existing IR map produces one actual `ValueRef`;
   claim-anchor equality alone is not proof of runtime-material equality;
9. author labels and discharge selectors are face-prefixed as carrier names,
   then `ReductionClosureOK` and `TerminalClosureOK` are re-judged over the open composite. Canonical
   terminal references are recomputed from positions, terminal-rule ids remain
   content-pinned through the unified vocabulary, and a selected check may not
   be silently shared across the linked faces (the exact producer/output
   exception remains local to one matched reduction and discharge);
10. construction routes compose under the same namespace and port maps as the
    spine. Witness declarations and hole instances are face-prefixed,
    references are rewritten to their exact composite targets, and cited
    HoleContracts remain content-pinned. The merged route graph is re-checked
    for exact parameters, segments, classes, counts, anchors, dependencies,
    acyclicity, declared slot-binding consistency, and handle linearity. An
    unmapped reference, a conflicting declaration, or a rewrite that gives a
    consumed handle another reader refuses. `link` never silently drops a
    surviving construction route; and
11. the composite is a new OPEN protocol; its identity is the seal's,
   afterwards.

## 4. descend *(reserved)*

A sealed artifact's realized verifier face becomes relation material
for an outer protocol. Rules:

1. claims and ABI facts transfer **by reference only** (artifact
   digest citation) — never re-derived, never widened;
2. the child's residual/export/assumption routes are either
   discharged by the outer verification semantics, imported as outer
   assumptions, or re-exported — LIN at the outer artifact accounts
   for them;
3. **recursion-gap visibility**: if the outer relation instantiates a
   random oracle heuristically in-circuit, the post-seal derivation
   covering the outer protocol MUST carry the corresponding assumption
   as an explicit inherited hypothesis;
4. self-referential recursion identity is a named extension (kernel
   §12); descend refuses digests it cannot ground.

## 5. Conformance tiers

The conformance ladder is:

```text
Tier 0  static projection feasibility
Tier 1  structural projection witness (valid ProjectionRows)
Tier 2  reference interpreter + golden/negative vectors
Tier 3  backend event log / semantic digest
Tier 4  fast-path translation validation
Tier 5  verified lowering subset
```

An implementation-level conformance or release claim for canonical OIR
requires repository evidence at Tiers 0–2. An individual OIR artifact carries
no Tier-2 receipt: its validity check authenticates identity and enforces the
carrier and structural projection rules. Optimized backend artifacts claim OIR
preservation only with Tier 3 or 4. Backend decision equality alone is never
Tier 3/4 evidence.

**Challenge noninterference** is a Tier-2+ obligation: the
negative half of Binding Lemma (a-determinism), "no value outside the
absorbed prefix influences a squeezed challenge", is a 2-safety
property of the endpoint program, checkable by taint or
self-composition over the reference interpreter. It is a conformance
obligation of the projection's *output*, which is why it is not an
additional seal judgment (kernel §9.2).

## 6. Backend realization contract *(reserved)*

`oir-realize` is the future boundary from canonical endpoint semantics to a
concrete backend or deployment artifact:

```text
oir-realize(OIRArtifact, ProjectionContext, target, backend_capabilities)
  -> BackendArtifact + ConformanceEvidence
```

`ProjectionContext` authenticates the sealed PIR artifact named by OIR's
source identity and reconstructs its projection obligations, claims,
reductions, and counterparty routes. It may be supplied as that sealed artifact
plus deterministic derived views; a bare source digest is not sufficient for
claim- or reduction-level preservation evidence.

This revision reserves the boundary and defines no stable backend-artifact
encoding. Backend names, concrete field/hash/PCS libraries, deployment targets,
layouts, and recipes enter here or below; they do not enter canonical OIR
identity unless they are already semantic registry names consumed by OIR
itself. A realizer must authenticate the OIR identity before reading the
program.

### 6.1 Optional Schedule and Kernel layers

A realizer may insert an internal scheduling layer to group compatible checks,
parallelize pure computation, choose layouts and kernels, plan already-declared
aggregation, or attach resource profiles. Those layers are optional; direct
realization is valid if it preserves the same contract and supplies the
required evidence.

Scheduling must not silently change:

```text
transcript prefixes or challenge domains
proof-slot order, codecs, or EOF behavior
public-statement binding
claim and counterparty routes
artifact-verification effects
terminal decision behavior
```

Protocol transformations such as introducing a new batch reduction belong in
PIR and the checked Compiler Core, not in an OIR scheduler. A schedule may fuse
or replace existing endpoint work only under explicit coverage/equivalence
evidence.

### 6.2 `FastPathCoverage` *(provisional schema)*

A backend fast path replaces reachable canonical OIR events; it never creates
missing endpoint semantics. Its eventual evidence must identify:

```text
covered OIR events and their source PIR positions
covered claims and reductions
transcript equivalence
proof-ABI equivalence
public-IO equivalence
check equivalence
artifact-verification equivalence, when present
claim/counterparty-route equivalence
decision equivalence
unsupported modes and explicit assumptions
evidence reference
```

The transcript-equivalence grade must be explicit (`byte_for_byte`,
`semantic_digest`, or a separately governed audited relation). Covered OIR
events must be reachable in the authenticated input artifact. Decision equality
alone is insufficient because it says nothing about transcript, proof ABI,
public binding, check coverage, artifact verification, or routes.

This is a preservation contract, not a serialized format. A backend lowering
must fix its schema and versioning before claiming Tier 3 or Tier 4 conformance.
An evaluation adapter or evidence producer does not by itself satisfy
`oir-realize` or mint a backend artifact.
