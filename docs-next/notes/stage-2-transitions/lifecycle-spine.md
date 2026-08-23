# Stage 2 lifecycle spine

> **Document kind:** Temporary architecture research note
> **Document state:** Reconstructive and generative; not converged
> **Authority:** None. This note records current correspondence evidence and
> clean-sheet contract hypotheses. It does not define a normative lifecycle,
> authenticate or admit an artifact, select public APIs, or authorize an
> implementation migration.
> **Stage 1 dependency:** The selected
> [Protocol IR Architecture](../../project/protocol-ir-architecture.md)
> remains fixed unless a named falsifier formally reopens it.
> **Disposition:** Review with the other Stage 2 workstreams, promote only
> converged contracts into their exact durable owners, then delete this note.

## 1. Question and scope

This note asks how a Protocol moves from human or machine proposal to a
canonical, authenticated, admitted, persisted, decoded, and consumer-usable
subject under the Stage 1 architecture.

It covers:

- authoring and import;
- resolution and normalization;
- canonical candidate formation;
- authentication and whole-Protocol admission;
- persistence, decoding, replay, and cross-process re-admission;
- purpose-specific consumer views;
- reopening and authority discard;
- authoring-level static link and semantic composition; and
- successor re-authentication and re-admission after checked change.

It deliberately does not design the complete PIR grammar, composition
algebra, semantic dependency schemas, Analysis result language, compiler
relation catalog, OIR schema, or evidence system. Those owners receive exact
lifecycle seams from Stage 2 and complete their internal models later.

This is architecture research, not defect or security review. Current
limitations are used as design pressure; they are not vulnerability claims.

## 2. Method and claim discipline

The note separates three layers:

1. **Observed current contracts** are reconstructed from the current
   specifications, implementation, tools, and tests.
2. **Inherited Stage 1 decisions** constrain the target but do not specify its
   transition signatures.
3. **Target hypotheses** are clean-sheet proposals. They are evaluated by
   explicit scenarios and falsifiers rather than by implementation
   convenience or migration cost.

Current tests establish implementation correspondence only for their exercised
cases. They do not make the target model normative and do not establish
soundness, completeness, source correspondence, endpoint correctness, or
portable admission authority.

The outcome vocabulary used below is intentionally non-binary:

| Outcome | Meaning |
|---|---|
| `Success` | The transition reached its subject and produced exactly its declared result. |
| `NegativeJudgment` | A judgment procedure successfully established a negative answer; this is not a failed transition. |
| `Malformed` | The representation cannot form the transition's source type. |
| `Unsupported` | The source is well formed, but its schema, regime, construct, target, or question is outside the implementation's declared domain. |
| `Unauthenticated` | Claimed identity, canonical form, or dependency closure does not match independently recomputed facts. |
| `Inadmissible` | An authenticated Protocol fails the normative whole-Protocol predicate of its exact semantic regime. |
| `Refused` | A transition-specific precondition or compatibility relation is false. This does not invalidate an otherwise admitted source. |
| `CannotAnswer` | Required authority, dependency preimage, checker, resource, or observation is unavailable, so no semantic answer was reached. |
| `OperationalFailure` | The procedure failed for a non-semantic reason such as I/O or resource exhaustion. Any externally visible partial effect must be reported explicitly. |

No transition may turn `CannotAnswer` into a negative semantic result or turn a
typed refusal into general Protocol invalidity.

## 3. Fixed Stage 1 intake

The target hypotheses inherit these decisions:

- a rich MLIR authoring/import/synthesis workbench is distinct from a small,
  closed canonical PIR level in MLIR;
- Protocol meaning is language-independent, while MLIR is the v0 structural
  carrier;
- `Protocol = InteractiveCore + ChallengeInterpretation`;
- a Core owns one total observable schedule;
- canonical PIR has one legal operation graph per Protocol and semantic regime,
  modulo MLIR object identity and SSA alpha-renaming;
- semantic identities are regime-qualified and independent of MLIR text and
  bytecode;
- `ProtocolInterface` and `ProverPlan` are separately identified subjects over
  an exact `ProtocolId`;
- authentication checks canonical profile, identities, and dependency closure;
- admission checks whole-Protocol semantics and mints an opaque immutable
  process-local capability;
- serialization never preserves that capability;
- reopening or mutation produces unauthoritative input that must cross the
  boundary again;
- consumers receive purpose-specific views rather than one universal fact
  root; and
- composition constructs a new Core and cannot inherit child identity or
  admission.

The identity factorization is therefore already fixed in shape:

```text
CoreId                    <- regime + canonical InteractiveCore
TranscriptConstructionId <- regime + CoreId + canonical construction
ProtocolId                <- regime + CoreId + challenge interpretation
ProtocolInterfaceId       <- interface regime + ProtocolId + interface
ProverPlanId              <- plan regime + ProtocolId + plan
```

Stage 2 must say when those identities first appear as claims, when they are
independently authenticated, what other inputs may affect each transition,
and what authority survives copying or serialization.

## 4. Observed current lifecycle

### 4.1 Current state graph

The current implementation is organized around one open PIR dialect shape and
one sealed spelling of substantially the same shape:

```text
textual pir.protocol or generated Open PIR
        |
        | SealEngine(environment): judge + resolve + identify + clone
        v
raw pir.sealed with stored id and cited vocabulary digests
        |
        | writeArtifact
        v
MLIR bytecode
        |
        | loadArtifact: decode + verify shape + recompute stored id
        v
DecodedPirArtifact
        |
        | admitArtifact(environment): registry-backed recheck
        v
AdmittedPirArtifact
        |
        +--> owned soundness or proof-read view
        +--> paired PIR-to-OIR projection capability
        +--> checked compiler successor
        `--> mutable reopened Open PIR clone

Open PIR + Open PIR
        |
        | LinkEngine(environment, face prefixes)
        v
new Open PIR -> ordinary seal path
```

The current `pir.protocol` to `pir.sealed` transition is not the physical
authoring-to-canonical level selected by Stage 1. The operation body is cloned
rather than rewritten into a distinct closed normal-form graph. The canonical
encoder instead computes a quotient over parts of the authored representation.

### 4.2 Current transition ledger

| Current transition | Actual source and reads | Successful result | What it currently establishes | Evidence |
|---|---|---|---|---|
| Direct authoring | Text parsed as `pir.protocol` | Mutable Open PIR | Carrier formation and structural verification only | [`PirOps.td`](../../../include/zkc/Dialect/Pir/PirOps.td), [`ToolUtils.h`](../../../include/zkc/Tools/ToolUtils.h) |
| FRI family generation | Declarative JSON plus the built-in template | Generated vocabulary text and Open PIR text | The vocabulary passes its real registry parser and the spine passes the real PIR parser; the generator explicitly remains unjudged | [`zkc-family.cpp`](../../../tools/zkc-family/zkc-family.cpp), [`fri-family.test`](../../../test/Family/fri-family.test) |
| Seal | `pir.protocol` plus one immutable `ProtocolEnvironment` | Raw `pir.sealed`; successful seal erases the input operation | Structural verification, whole seal battery, construction-graph checks, resolution of cited vocabulary and construction-profile digests, canonical-ID computation, and sealed carrier formation are fused | [`SealEngine.cpp`](../../../lib/Semantics/SealEngine.cpp), [`pir-seal.mlir`](../../../test/Transforms/pir-seal.mlir), [`seal-engine-parity.test`](../../../test/Transforms/seal-engine-parity.test) |
| Raw ID or canonical translation | Raw open or sealed carrier | Diagnostic bytes or ID | Computes an identity projection; it confers no acceptance capability | [`CanonicalEncoder.h`](../../../include/zkc/Encoding/CanonicalEncoder.h), [`normalization.mlir`](../../../test/Encoding/normalization.mlir) |
| Persist | Raw `pir.sealed` plus an output stream | MLIR bytecode with a producer marker | Recomputes the stored ID before writing; it does not repeat registry-backed admission | [`Artifact.cpp`](../../../lib/Artifact/Artifact.cpp), [`roundtrip.mlir`](../../../test/Artifact/roundtrip.mlir) |
| Decode | Bytecode, optional expected ID, PIR dialect decoder | Copy-only opaque `DecodedPirArtifact` | Checks bytecode framing, a `zkc_v` producer prefix, exact one-root `pir.sealed` shape, structural verification, dialect transport version, recomputed ID, and optional caller selection. It does not run the registry-backed seal judgment | [`Artifact.h`](../../../include/zkc/Artifact/Artifact.h), [`Artifact.cpp`](../../../lib/Artifact/Artifact.cpp), [`fail-closed.test`](../../../test/Artifact/fail-closed.test) |
| Admit | `DecodedPirArtifact` plus a `ProtocolEnvironment` | Copy-only opaque `AdmittedPirArtifact` | Re-runs the seal battery, construction graph, exact cited-authority matching, and ID validation, then binds the immutable decoded subject to the retained environment | [`Artifact.cpp`](../../../lib/Artifact/Artifact.cpp), [`lifecycle.mlir`](../../../test/Artifact/lifecycle.mlir), [`TestArtifactLifecycle.cpp`](../../../test/lib/TestArtifactLifecycle.cpp) |
| Derive soundness view | `AdmittedPirArtifact` | Owned MLIR-free `SealedSoundnessView` | Derives the facts selected by the adapter for later Analysis; it does not itself establish a property judgment | [`PirSoundnessAdapter.cpp`](../../../lib/Soundness/PirSoundnessAdapter.cpp), [`soundness.md`](../../../docs/spec/soundness.md) |
| Derive proof-read view | `AdmittedPirArtifact` and its retained construction-profile environment | Immutable observation vector | Resolves registry-qualified verifier proof reads in canonical event order | [`ProtocolArtifacts.cpp`](../../../lib/Dialect/Pir/Transforms/ProtocolArtifacts.cpp) |
| Project | `AdmittedPirArtifact`, endpoint kind, and current environment | Copy-only paired `ProjectedOirArtifact` plus durable OIR carrier | Constructs a new OIR subject while retaining source-relative projection authority in process | [`Projection.h`](../../../include/zkc/Dialect/Pir/Transforms/Projection.h), [`PirProject.cpp`](../../../lib/Dialect/Pir/Transforms/PirProject.cpp), [`project.test`](../../../test/Artifact/project.test) |
| Reopen | `AdmittedPirArtifact` | Independent mutable clone containing a new Open PIR sibling | Copies body and protocol fields but deliberately omits resolved vocabulary authority; the source capability remains valid | [`ProtocolArtifacts.cpp`](../../../lib/Dialect/Pir/Transforms/ProtocolArtifacts.cpp), [`TestArtifactLifecycle.cpp`](../../../test/lib/TestArtifactLifecycle.cpp) |
| Static link | Two Open PIR roots, face prefixes, and one environment | New Open PIR | Judges both inputs, namespaces labels and challenge domains, fuses exact matching faces, combines schedule segments and routes, and transactionally returns an unauthoritative composite | [`LinkEngine.cpp`](../../../lib/Semantics/LinkEngine.cpp), [`pir-link.mlir`](../../../test/Transforms/pir-link.mlir), [`pir-link-routes.mlir`](../../../test/Transforms/pir-link-routes.mlir) |
| Checked compiler successor | Admitted predecessor, exact transform family and request, current environment | Reopened, changed, sealed, snapshotted, re-admitted successor; checker replays and compares | A successful transform-family check relates exact predecessor and successor artifacts; successor admission is reconstructed rather than inherited | [`PirCompilerProvider.cpp`](../../../lib/Compiler/PirCompilerProvider.cpp), [`compiler.md`](../../../docs/spec/compiler.md) |

The current normative boundary notation is summarized in
[`boundaries.md`](../../../docs/spec/boundaries.md): raw Open PIR is checked at
entry unless an opaque authenticated capability substitutes; failures produce
diagnostics and no partial semantic artifact; static link returns Open PIR that
must be sealed normally.

### 4.3 Current authority and identity observations

1. **Seal currently fuses several logical claims.** `SealEngine::seal` first
   judges the open protocol, constructs the exact cited vocabulary table,
   temporarily installs it for identity computation, clones the body into a
   `pir.sealed`, and erases the open root on success. Failure restores the
   authored vocabulary state. Resolution, semantic validation, identity mint,
   and carrier-state change therefore share one implementation operation.

2. **The canonical identity is stronger than raw text but weaker than the
   selected physical-normal-form boundary.** The encoder normalizes author
   labels, source/reduction/sink ordering, dependency lists, and positional
   references. [`relabel.mlir`](../../../test/Encoding/relabel.mlir),
   [`normalization.mlir`](../../../test/Encoding/normalization.mlir), and
   [`reduction-normalization.test`](../../../test/Encoding/reduction-normalization.test)
   exercise equal IDs for distinct carrier representatives. Stage 1 instead
   requires normalization to emit the one legal canonical graph and requires
   authentication to reject noncanonical representatives.

3. **Identity cites a consumed subset; admission retains a larger provider.**
   The sealed root contains exact digests for cited vocabulary and construction
   entries. Admission accepts an otherwise identical environment with an
   uncited addition and refuses a changed cited entry. The admitted capability
   nevertheless retains the complete `ProtocolEnvironment`, so later consumers
   can currently read more than the minimal admission basis.

4. **Persistence is identity-checked but not admission-gated at its library
   type boundary.** `writeArtifact` accepts any raw `pir.sealed` whose stored
   ID recomputes. The normal `zkc-seal` producer obtains that value through
   `SealEngine`, but the library writer does not require `AdmittedPirArtifact`.

5. **Decode and admission already have separate opaque types.** Both decoded
   and admitted handles are copy-only wrappers over private shared immutable
   storage. No public IR accessor exists. The `SealedGuard` blocks
   action-dispatched pattern rewrites under raw sealed roots, while its own
   contract acknowledges that direct C++ mutation is not intercepted;
   capability opacity and storage isolation are the primary boundary.

6. **Serialization ends capability continuity.** The loader returns decoded,
   not admitted, authority. A fresh `ProtocolEnvironment` is required to mint
   a new admitted capability. The producer marker is diagnostic provenance,
   not an acceptance rule, and MLIR bytecode is not the Protocol identity
   surface. The current v0 dialect transport accepts exactly its declared
   version and has no upgrade path; see
   [`versioning.md`](../../../docs/spec/versioning.md).

7. **Reopening branches rather than revokes.** The mutable clone drops resolved
   vocabulary so that later seal resolves authority again. The original
   admitted handle remains valid because its storage is independent. Thus
   “discard admission” applies to the editable descendant, not to the source
   capability.

8. **Static link is an authoring transition.** It checks enough current
   semantics to construct a coherent result, but neither child identity nor
   authority is inherited. The output is Open PIR and must be sealed again.

9. **Purpose-specific views are present but their input closure is not yet the
   selected Stage 1 closure.** The soundness adapter's view includes statement
   labels and material-to-label mappings, while the current Protocol identity
   intentionally erases author labels. Stage 1 resolves this architectural
   pressure by requiring interface-sensitive consumers to receive an exact
   `ProtocolInterfaceId` or to stop reading those fields.

10. **Import is not yet a general lifecycle boundary.** Current supported
    ingress is direct low-level PIR authoring plus a parameterized FRI family
    generator. Generic source DSLs, foreign-IR importers, and source
    correspondence judgments remain planned work rather than implemented
    authority.

## 5. External mechanism constraints

These external sources constrain mechanisms; they do not define zkc semantic
authority.

- [MLIR dialect conversion](https://mlir.llvm.org/docs/DialectConversion/)
  can enforce that every operation in a full conversion is legal in the chosen
  target. It is suitable for the final authoring-to-canonical legality gate,
  but it does not establish zkc's whole-Protocol predicate.
- [MLIR canonicalization](https://mlir.llvm.org/docs/Canonicalization/) is a
  best-effort rewrite infrastructure with no promise of reaching a globally
  unique form. It cannot define the Stage 1 physical canonical PIR contract.
- [MLIR bytecode](https://mlir.llvm.org/docs/BytecodeFormat/) is a versioned
  container with a producer field and dialect-owned versioning. Successful
  decoding does not imply semantic identity, dependency closure, or admission.
- [RFC 6920](https://datatracker.ietf.org/doc/rfc6920/) gives a useful limit:
  a digest can name and integrity-check bytes, but that fact alone does not
  establish semantic correspondence, admission, or authority to rely on the
  named object.

The target should use these mechanisms at their actual strength rather than
promote transport or rewrite machinery into semantic judgment.

## 6. Proposed target lifecycle

Everything from this section onward is a target hypothesis, not an observation
about the current implementation.

### 6.1 Governing principles

1. **One transition, one primary postcondition.** A physical implementation
   may fuse scans or allocate one object, but the logical result types must not
   conflate representation formation, identity authentication, semantic
   admission, or consumer judgment.
2. **No ambient reads.** Every value whose change can affect a result is an
   explicit input or is immutably carried by an authenticated input
   capability.
3. **Authority is not identity.** `ProtocolId` names a semantic subject;
   `AdmittedProtocol` authorizes process-local use of one immutable
   representation of that subject under an exact admission basis.
4. **Bytes do not carry capabilities.** Cross-process use always reconstructs
   authority, even when semantic identity and transport integrity are intact.
5. **Normalization is not admission.** It may validate source distinctions
   before erasure, but an independently checkable canonical result must still
   authenticate and admit without trusting the normalizer's search or witness.
6. **Minimal retained closure.** An admitted capability retains the exact
   semantic regime and dependency basis needed to justify admission, not an
   ambient resolver that future consumers may query opportunistically.
7. **New semantic subject, new admission.** Reopen, checked change, link, and
   composition never inherit predecessor or child authority for their output.
8. **Official persistence has one grade.** Canonical deployable Protocol
   artifacts are producer-side admission-gated. Unadmitted candidates, if a
   workflow needs them, use a distinctly named workbench/cache envelope.
9. **Failure is typed and transactional at semantic boundaries.** Diagnostics
   may survive; a partially authenticated, partially admitted, or partially
   persisted Protocol may not.

### 6.2 State machine

```text
explicit authored inputs                 external source subject
          |                                        |
          | Author                                 | Import(importer semantics)
          +------------------+---------------------+
                             v
                        AuthoringUnit
                             |
                             | Resolve(exact immutable snapshot)
                             v
                   ResolvedAuthoringUnit
                   + ResolutionClosure
                             |
                             | Normalize(profile, explicit selections)
                             v
             CanonicalProtocolCandidate              side outputs
             + claimed semantic identities     +--> InterfaceCandidate(s)
             + complete dependency manifest    +--> ProverPlanCandidate(s)
                                               +--> source map / provenance
                                               `--> optional relation witness
                             |
                             | Authenticate(regime, dependency preimages)
                             v
                  AuthenticatedCanonicalProtocol
                             |
                             | Admit(normative regime checker)
                             v
                        AdmittedProtocol
                         /      |       \
                        /       |        \
           DeriveView /    Persist       \ Reopen
                      v         v          v
                ConsumerView  canonical   AuthoringUnit
                              artifact    (raw branch)
                                |
                                | new process
                                v
                       Decode -> Authenticate -> Admit
```

The boundaries are logical. For example, an in-process `normalizeAndAdmit`
API may share traversal and memory, but it must be explainable as producing the
same intermediate claims and refusals as the state machine above.

### 6.3 Proposed state contracts

| State | Formation and content | Authority |
|---|---|---|
| `AuthoringUnit` | Mutable, possibly partial, mixed-dialect, family-valued, or unresolved proposal | None; no stable `ProtocolId` |
| `ResolvedAuthoringUnit` | Immutable snapshot of one authoring proposal after named references are resolved against an exact resolver snapshot; carries an explicit `ResolutionClosure` | Resolution provenance only; not a Protocol identity or admission |
| `CanonicalProtocolCandidate` | Immutable closed canonical PIR graph, exact semantic regime, complete typed dependency manifest, and claimed compositional IDs | Claims identity but has no authentication or admission authority |
| `DecodedCanonicalCarrier` | Immutable carrier decoded under one exact transport schema | Transport formation only; no semantic authority |
| `AuthenticatedCanonicalProtocol` | Opaque immutable candidate whose physical form, claimed IDs, regime, and dependency closure were independently recomputed | Authorizes admission and identity-preserving representation use; does not assert semantic admissibility |
| `AdmittedProtocol` | Opaque immutable authenticated subject plus minimal exact `AdmissionBasis` | Authorizes consumers that require whole-Protocol admission; does not establish downstream properties |
| `ConsumerView<Q>` | Immutable, question-scoped derivation from an admitted source and all explicit auxiliary inputs | Authorizes only consumer `Q`; not a general Protocol capability |
| `PersistedCanonicalProtocol` | Versioned transport envelope containing canonical carrier bytes, claimed semantic IDs, and optional transport digest | No process-local authority; producer-side API discipline is not portable proof |

`AdmissionBasis` should contain the exact semantic regime, verified dependency
closure identifiers/preimages or an immutable handle to them, and the checker
contract needed to explain the admission. It should not retain an open-ended
registry merely because the implementation loaded one.

### 6.4 Ownership, classification, and effects

These are provisional semantic owners, not proposed C++ namespaces. A bridge
whose result is consumed by another domain still needs review by both endpoint
owners.

| Transition | Provisional owner | Classification and cardinality | Determinism and effects |
|---|---|---|---|
| `Author` | Authoring/workbench | Proposal formation; many fragments to one mutable unit | Result is determined by explicit inputs, though an interactive editor may issue many such actions; workbench-local mutation only |
| `Import` | Importer, reviewed with authoring and external-source owners | Interpretation plus proposal formation; one external snapshot may yield one unit and several side records | Deterministic under exact importer semantics and options; no external effect after the source snapshot is bound |
| `Resolve` | Authoring/PIR ingress | Environment interpretation; one unit to one resolved snapshot and one closure | Deterministic over one immutable resolver snapshot; read-only |
| `Normalize` | PIR | Representation/elaboration or selected-member construction; one resolved proposal to one Protocol candidate plus typed side outputs | Deterministic over exact profile and choices; transactional construction |
| `Authenticate` | PIR identity and dependency authority | Authentication; one candidate or decoded carrier to one opaque handle | Deterministic and read-only; may share traversal with admission |
| `Admit` | Protocol semantic regime/PIR admission service | Whole-subject admission; one authenticated Protocol to one capability | Deterministic under exact regime; process-local capability allocation only |
| `PersistProtocol` | PIR artifact transport | Representation; one admitted subject to one durable artifact | Semantic result deterministic, byte spelling need not be; atomic I/O is the only external effect |
| `Decode` | PIR artifact transport | Representation formation; bytes to one immutable carrier | Deterministic under exact schema and resource bounds; read-only I/O |
| `DeriveView` | Consuming domain, reviewed with Protocol owner | Scoped derivation or judgment; one admitted source plus explicit auxiliaries to one typed result | Deterministic under exact question/checker; no hidden cache authority |
| `Reopen` | PIR/workbench | Authority-discarding representation change; one admitted source to one raw branch | Canonical content recovery is deterministic; allocates independent mutable storage |
| `LinkAuthoringUnits` | Authoring/workbench | Proposal construction; many authoring occurrences to one authoring unit | Deterministic under exact link plan; transactional and input-preserving |
| `ComposeAdmittedProtocols` | Protocol composition owner, reviewed with PIR | Semantic construction; many admitted occurrences to one new candidate | Deterministic under exact composition plan and regime; child capabilities remain valid |
| Checked successor | Compiler owns proposal/relation; PIR owns successor authentication/admission | Checked semantic change; predecessor plus request to successor and named relation | Search may vary, but accepted result and checker outcome are deterministic over declared comparison inputs |

Except for explicitly reported artifact I/O, these lifecycle transitions have
no external operational effects. Endpoint invocation, deployment, evidence
recording, and partial operational failure belong to other Stage 2 bridges.

## 7. Proposed transition contracts

### 7.1 Author and import

```text
Author(explicit source fragments, authoring profile, explicit options)
  -> AuthoringUnit | AuthoringRefusal | CannotAnswer

Import(external subject snapshot,
       ImporterSemanticsId,
       explicit import options,
       importer dependencies)
  -> AuthoringUnit
   + ImportProvenance
   + optional CorrespondenceProposal
   | ImportRefusal | CannotAnswer
```

Both transitions produce unauthoritative workbench content. Neither creates a
`ProtocolId`, and successful parsing or generation does not establish that a
Protocol is admissible.

Import has a stronger provenance obligation than authoring because it claims
to interpret another subject. The importer semantics, exact source snapshot,
and all interpretation options must be explicit. Any source-to-target
correspondence is a separate proposed or checked relation; it is not implied by
possession of the imported target. If the external language is family-valued
or underspecified, import must preserve that openness or require an explicit
selection rather than silently choosing one Protocol.

### 7.2 Resolve

```text
Resolve(AuthoringUnit,
        ResolverSnapshot,
        ResolutionProfile)
  -> ResolvedAuthoringUnit
   + ResolutionClosure
   | ResolutionRefusal | Unsupported | CannotAnswer
```

Resolution is environment-sensitive and normalization is not. `Resolve` must:

- read only one immutable resolver snapshot;
- enumerate every authoring resource actually consulted;
- classify each resulting dependency by the closure classes in Section 8;
- detect missing, ambiguous, incompatible, or cyclic references according to
  the exact schema;
- materialize identity-bearing semantic dependency preimages or exact
  content-addressed references to them; and
- record authoring-only resources in provenance without accidentally making
  the entire resolver part of Protocol identity.

An uncited addition to the resolver snapshot must not change the resolved
result. If lookup priority or enumeration order can change the result, that
priority or order is an identified input rather than ambient behavior.

`ResolutionClosure` is not a universal environment ID. It is a typed manifest
of what this resolution actually read and how each item is classified.

### 7.3 Normalize and form a canonical candidate

```text
Normalize(ResolvedAuthoringUnit,
          ProtocolSemanticRegimeId,
          NormalizationProfile,
          explicit ChoiceVector)
  -> CanonicalProtocolCandidate
   + ExtractedSubjects
   + SourceMap
   + optional NormalizationWitness
   | NormalizationRefusal | Unsupported | CannotAnswer
```

Normalization is deterministic over its complete inputs. It performs the
information-loss-frontier checks before erasing source distinctions, selects
exactly one total observable schedule and challenge interpretation, eliminates
all authoring-only and foreign operations, makes defaults explicit, emits the
complete typed dependency manifest, and produces the one legal canonical PIR
graph modulo allowed carrier trivia.

MLIR full dialect conversion may enforce the final operation allowlist.
Generic MLIR canonicalization may help implement local rewrites but cannot
define completion or uniqueness.

The normalizer computes and places the candidate's claimed `CoreId`, optional
`TranscriptConstructionId`, and `ProtocolId`. These are unauthenticated claims
until the next transition independently recomputes them. Interface labels,
external packaging, plan-local algorithms, source locations, and provenance
leave through typed side outputs; they do not survive as hidden canonical
carrier context.

The relation from source to candidate is not always `RepresentationEq`:

- elaboration of a fully denoting source may propose
  `RepresentationEq(source denotation, candidate)`;
- choosing one member of a family proposes `SelectedMember`;
- an intentional semantic choice may require another named relation; and
- import correspondence remains separate from all three.

The optional witness can support a source-relative checker, but target
authentication and admission must not trust it. The canonical candidate must
be independently checkable from its own graph, regime, and dependency
preimages.

### 7.4 Authenticate

```text
Authenticate(CanonicalProtocolCandidate | DecodedCanonicalCarrier,
             expected ProtocolSemanticRegimeId,
             exact semantic dependency preimages,
             optional expected semantic identities)
  -> AuthenticatedCanonicalProtocol
   | Malformed | Unsupported | Unauthenticated | CannotAnswer
```

Authentication answers one question:

> Is this immutable carrier exactly the canonical Protocol subject that its
> regime, manifest, and semantic identity claims name?

It checks:

- the closed canonical PIR allowlist and physical normal form;
- one explicit, supported semantic regime;
- exact direct dependency citations and the required reachable closure;
- content identities of all identity-bearing semantic dependency preimages;
- absence of unresolved, foreign, authoring-only, interface-only, plan-only,
  and unclassified fields;
- recomputed Core, construction, and Protocol identities for the canonical
  Protocol subject; separately extracted Interface and Plan candidates cross
  their own authentication boundaries; and
- optional expected IDs supplied by a caller selecting a subject.

Authentication does not establish whole-Protocol admissibility, source or
import correspondence, soundness, completeness, relation truth, endpoint
support, projection coverage, or suitability under a local policy.

The distinction from admission is logical rather than a demand for duplicate
work. One checker implementation may share decoding, indexing, and traversal,
but it must expose the two postconditions and their refusals separately.

### 7.5 Admit

```text
Admit(AuthenticatedCanonicalProtocol,
      exact normative checker for ProtocolSemanticRegimeId)
  -> AdmittedProtocol
   | Unsupported | Inadmissible | CannotAnswer
```

Admission checks the complete normative whole-Protocol predicate under the
exact regime, including closed types and ports, schedule and causal rules,
protected effects, claims/reductions/checks/terminals, challenge
interpretation, dependency use, failure outcomes, and abstract endpoint
obligation completeness.

Admission preserves every semantic identity and mints no new semantic
subject. Its only new authority is a process-local opaque immutable capability.
Local deployment or relying policy must remain a later decision: it may refuse
an admitted Protocol, but it cannot change whether that Protocol satisfied the
named semantic regime.

### 7.6 Persist, decode, and re-admit

The working default is a two-envelope policy:

```text
PersistProtocol(AdmittedProtocol, exact TransportSchema)
  -> PersistedCanonicalProtocol | Unsupported | OperationalFailure

PersistWorkbench(CanonicalProtocolCandidate or AuthoringUnit,
                 explicit cache schema)
  -> UnauthoritativeWorkbenchCache | OperationalFailure
```

Only the first is a canonical deployable Protocol artifact. The second exists
only if a real workflow needs durable intermediate candidates and is visibly
not an admitted artifact kind.

`PersistProtocol` preserves semantic IDs but destroys process-local capability
continuity. It may compute a transport digest for byte integrity. That digest
is not `ProtocolId`, and v0 need not promise identical bytecode across producer
releases or equivalent transport encodings.

```text
Decode(bytes, exact TransportSchema)
  -> DecodedCanonicalCarrier
   | Malformed | Unsupported | OperationalFailure
```

Decode safely forms one immutable carrier under one exact transport schema. It
checks framing, resource bounds, transport version, carrier formation, and any
transport digest. An implementation may also short-circuit obvious semantic-ID
mismatches or an expected-ID mismatch for diagnostics, but the returned type
does not gain semantic authentication until `Authenticate` has checked the
regime and dependency closure.

A consumer therefore runs:

```text
bytes -> Decode -> Authenticate -> Admit -> consumer
```

The producer release is diagnostics or provenance, not a semantic gate. No
serialized admission receipt is proposed for v0. A future independent consumer
that cannot rerun admission would trigger a separate, claim-scoped certificate
design rather than changing the meaning of these bytes.

### 7.7 Derive a consumer view

```text
DeriveView(ViewSchemaId,
           AdmittedProtocol,
           explicit ProtocolInterface or ProverPlan when needed,
           explicit consumer authority and question)
  -> ConsumerView<Question>
   | NegativeJudgment | Unsupported | Refused | CannotAnswer
```

A view contains only the facts needed for one named consumer question, the
source `ProtocolId`, exact auxiliary subject IDs, scope, and derivation regime.
It may not read ambient author labels, a retained resolver, or arbitrary MLIR
attributes. If a consumer needs application labels or ABI packaging, it must
receive an authenticated `ProtocolInterface`; if it needs prover construction
choices, it must receive an authenticated `ProverPlan`.

An ephemeral in-process view has no independent semantic identity. If a view
must cross a process boundary or support independent reliance, it becomes a
domain-owned artifact or certificate with its own subject, identity, checker,
and refusal contract. It does not become a general `AdmittedProtocol` token.

A source-free OIR or other target can establish its own shape and local
validity. It cannot establish that all source obligations were projected
without an admitted source or sufficient source-bound evidence; the proper
result is `CannotAnswer`, not inferred coverage.

### 7.8 Reopen and discard authority

```text
Reopen(AdmittedProtocol)
  -> AuthoringUnit(origin = ProtocolId as non-authoritative provenance)
   | OperationalFailure
```

Reopen creates an independent mutable proposal. The old `ProtocolId` may be
recorded as lineage, but it is not an active identity claim on the draft. The
original admitted capability remains valid; only the editable branch lacks
authority.

A no-op branch normalized under the same regime, exact dependency preimages,
normalization profile, and explicit selections should recover the same
semantic IDs. Any semantic change or regime change yields a new subject. The
result always authenticates and admits again even when the recovered ID is
equal.

### 7.9 Static link, semantic composition, and checked successors

Two operations should not share one ambiguous `link` contract.

```text
LinkAuthoringUnits(AuthoringUnit(s), explicit LinkPlan)
  -> AuthoringUnit | LinkRefusal | Unsupported | CannotAnswer
```

This is a workbench convenience. It may namespace source handles, connect
declared faces, and combine unresolved structures, but its output remains raw.
If it requires resolved meanings, its source type must instead be
`ResolvedAuthoringUnit` and its exact resolution closure must be explicit.

```text
ComposeAdmittedProtocols(AdmittedProtocol occurrences,
                         explicit CompositionPlan,
                         ProtocolSemanticRegimeId)
  -> CanonicalProtocolCandidate
   | CompositionRefusal | Unsupported | CannotAnswer
```

This is semantic construction. The plan must eventually specify occurrence
namespaces, child-to-composite face maps, causal seams, one total interleaving,
challenge independence or sharing, domain separation, failure/terminal
propagation, and the resulting dependency and endpoint-obligation closure.
Repeated use of one child is represented by distinct occurrences.

The result is a new Core candidate with new claimed identities. Child
admission is an input precondition, not inherited output authority. The
candidate must authenticate and admit as a whole. The exact composition
algebra and whether child IDs are direct identity preimage fields remain Stage
3 questions; the lifecycle invariant does not.

A compiler transform is another checked-change family, not composition. Its
proposer may search freely, but the chosen successor follows the same path:

```text
Admitted predecessor
  -> proposed successor candidate
  -> authenticate successor
  -> admit successor
  -> check named predecessor/successor relation
```

The relation checker may reuse authenticated views, but neither predecessor
admission nor a producer claim substitutes for successor admission.

## 8. Closure and read-set matrix

### 8.1 Closure classes

| Code | Closure | Target treatment |
|---|---|---|
| `W` | Explicit source/workbench fragments and authoring options | Inputs to authoring only; not Protocol identity merely because they were read |
| `I` | External source snapshot, importer semantics, and importer dependencies | Import provenance/correspondence inputs; not silently Protocol authority |
| `R` | Exact resolver snapshot and authoring-only resolution reads | Produces `ResolutionClosure`; unused resolver content has no effect |
| `D` | Identity-bearing Protocol semantic dependency preimages and their required reachable closure | Explicit manifest, content-authenticated, interpreted by authentication/admission |
| `O` | Opaque external subject references | Exact identifiers are Protocol content; referenced truth or interpretation is not acquired |
| `G` | Typed semantic regime and its normative checker contract | Explicit for normalize/authenticate/admit; regime changes cannot preserve semantic identity |
| `N` | Normalization profile and explicit choice vector | Explicitly determines one candidate; no hidden optimizer/search choice |
| `X` | `ProtocolInterface`, `ProverPlan`, or other dependent semantic subject | Separately identified input only where a transition needs it |
| `T` | Transport schema, resource limits, and optional transport-integrity parameters | Persistence/decode only; not Protocol meaning |
| `C` | Consumer question, checker, target, policy, theorem, or supplier authority | Explicit at the consumer transition; not retained as Protocol truth |
| `A` | Ambient mutable state, default registry enumeration, clock, randomness, process-global flags | Forbidden as a result-affecting read everywhere |

### 8.2 Transition read sets

The source state named by a row is implicit. `Required` means the class is a
direct input; `carried` means it is available only through an immutable input
capability; `IDs` means identifiers are read without acquiring subject
authority.

| Transition | `W` | `I` | `R` | `D` | `O` | `G` | `N` | `X` | `T` | `C` | `A` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `Author` | Required | — | — | — | — | authoring profile only | explicit options | — | — | — | Forbidden |
| `Import` | — | Required | optional, explicit | — | IDs if present | importer regime | explicit options | — | source transport if any | correspondence checker only if checked now | Forbidden |
| `Resolve` | carried | — | Required | produces | classifies IDs | schema regime | — | extracts only | — | — | Forbidden |
| `Normalize` | carried | carried provenance | carried closure | carried | IDs | Required | Required | emits separately | — | optional relation checker | Forbidden |
| `Authenticate` | — | — | — | Required or carried | IDs | Required | — | only subjects explicitly present | carrier schema, not transport bytes | optional expected IDs | Forbidden |
| `Admit` | — | — | — | carried exact basis | IDs | carried exact regime | — | — | — | normative admission checker | Forbidden |
| `PersistProtocol` | — | — | — | carried, not re-resolved | IDs in subject | carried | — | — | Required | — | Forbidden |
| `Decode` | — | — | — | not interpreted | not interpreted | claimed only | — | claimed only | Required | optional expected transport selector | Forbidden |
| `DeriveView` | — | — | — | carried minimum | IDs | carried | — | Required when question depends on it | — | Required | Forbidden |
| `Reopen` | produces new workbench | — | — | copied as proposals only | IDs/provenance | origin only | — | not silently merged | — | — | Forbidden |
| `LinkAuthoringUnits` | carried inputs | carried provenance | only if source type says resolved | carried only for resolved form | IDs | explicit authoring regime | link plan | explicit extracted bindings | — | — | Forbidden |
| `ComposeAdmittedProtocols` | — | — | — | carried from child capabilities plus explicit seams | child IDs | Required | composition plan | explicit interfaces if faces require them | — | composition checker | Forbidden |

### 8.3 Closure invariant

For every deterministic transition `F`, the following must hold:

```text
equal named source subjects
+ equal values for every declared read-set class
-------------------------------------------------
= equal semantic result and outcome category
```

Changes outside the declared read set may change diagnostics, timing, or
resource use, but not the semantic result. A counterexample is a closure bug in
the contract model and must add the missing input or remove the read.

## 9. Identity-effect matrix

| Transition | Semantic identities consumed | Identity effect on success | Capability effect | Intentionally excluded from semantic identity |
|---|---|---|---|---|
| `Author` | None required | None | Produces raw mutable proposal | Source path, time, editor state |
| `Import` | External source identity if defined | No Protocol identity; records source provenance separately | Produces raw mutable proposal | Importer execution trace and incidental source spelling |
| `Resolve` | Exact IDs/digests of resolved resources | No Protocol identity; fixes the candidate dependency inputs | Produces immutable resolved snapshot, not authority | Unread resolver entries and lookup cache layout |
| `Normalize` | Regime ID, semantic dependency IDs, explicit opaque refs | Computes candidate claims for Core, construction, Protocol, and extracted dependent subjects | No authority | Source locations, macro history, author labels, search trace |
| `Authenticate` | All claimed semantic IDs and dependency IDs | Recomputes and confirms them; mints no new semantic ID | Creates authenticated immutable capability | Checker binary version unless it changes the named regime |
| `Admit` | Authenticated Protocol and exact regime | Preserves semantic IDs | Creates process-local admitted capability | Local suitability policy and process identity |
| `PersistProtocol` | Admitted Protocol IDs | Preserves semantic IDs; may mint `TransportDigest` | Drops capability continuity in bytes | Producer release from Protocol meaning; byte layout from Protocol ID |
| `Decode` | Transport schema/digest; claimed semantic IDs as data | Mints no semantic ID and confirms no semantic authority | Creates immutable decoded carrier only | Decoder process identity |
| `DeriveView` | Protocol ID plus every explicit Interface/Plan/question ID | Ephemeral view normally has no new semantic ID; durable result uses domain-owned ID | Narrows authority to one question | Unrequested carrier facts and ambient registry state |
| `Reopen` | Origin Protocol ID as lineage | Drops active identity claim; later normalization recomputes same or new IDs | Produces raw mutable proposal; source capability unchanged | Edit history unless separately recorded |
| `LinkAuthoringUnits` | None required; source provenance optional | No Protocol ID | Produces raw authoring result | Child admission and IDs as authority |
| `ComposeAdmittedProtocols` | Child Protocol IDs, regime, exact composition plan | Computes claims for a new Core and Protocol | Child capabilities authorize reads only; output has no inherited authority | Capability object identity and incidental child carrier layout |
| Checked successor | Predecessor Protocol ID and transform inputs | Preserves or changes ID only according to the named relation; successor ID is independently recomputed | Successor re-authenticates and re-admits | Producer-authored score, cached verdict, and search history |

Two carriers with the same `ProtocolId` under the same regime denote the same
normative Protocol, but they need not have the same transport bytes,
`ProtocolInterfaceId`, `ProverPlanId`, process-local capability, provenance, or
consumer view.

## 10. Capability and lifetime matrix

| State | Mutability and aliasing | Lifetime/concurrency | Authority carried | Serialization result | Permitted next operations |
|---|---|---|---|---|---|
| `AuthoringUnit` | Mutable; unique ownership or explicitly synchronized workbench aliases | Workbench-local; concurrency is an authoring concern | None | Source/cache only, visibly unauthoritative | Edit, resolve, authoring link, discard |
| `ResolvedAuthoringUnit` | Immutable snapshot; safely shareable | Process-local or cacheable with explicit resolution schema | Exact resolution provenance only | Cache may preserve data, not Protocol authority | Normalize, inspect provenance, discard |
| `CanonicalProtocolCandidate` | Immutable value after formation | Shareable; mutation creates a new raw candidate | Claimed IDs only | Unauthoritative candidate cache if separately typed | Authenticate, inspect, discard |
| `DecodedCanonicalCarrier` | Immutable private storage | Copy/share across threads if implementation guarantees read-only carrier access | Transport formation only | Re-encoding yields bytes, still no authority | Authenticate, inspect safe diagnostics, discard |
| `AuthenticatedCanonicalProtocol` | Opaque immutable handle; copy may share immutable storage | Process-local and read-concurrent | Exact identity/canonical-closure authority | Serialization yields raw bytes, not the handle | Admit, compare identities, discard |
| `AdmittedProtocol` | Opaque immutable handle; copies preserve the same authority | Process-local and read-concurrent | Whole-Protocol admission under exact basis | Serialization yields bytes requiring re-authentication and re-admission | Derive scoped views, persist, compose, reopen, checked transform |
| `ConsumerView<Q>` | Immutable, normally owned MLIR-free data | Process-local; only consumer `Q` may rely on it | Named source-bound facts for `Q` | Raw data unless promoted to a domain-owned artifact/certificate | Run `Q`, compare within scope, discard |
| `PersistedCanonicalProtocol` | Bytes may be copied; any mutation invalidates transport integrity | Durable according to transport policy | None | It is already serialized | Decode only |
| Reopened branch | Independent mutable authoring storage | Workbench-local | Origin ID is provenance only | Source/cache only | Edit, resolve, normalize, discard |

There is no capability identity. A `ProtocolId` names semantic content, while
an admitted handle is an unforgeable process-local route to an immutable
subject and its exact basis. Copying that opaque handle may preserve authority;
copying its bytes or cloning its carrier does not.

Admission is historical under an exact regime and dependency closure. A later
regime or local policy can supersede suitability for a use, but it does not
retroactively change the old Protocol's identity or make a different regime's
admission result implicit.

## 11. Serialization and replay matrix

| Path or scenario | What may be replayed | Required result and non-claim |
|---|---|---|
| Same resolved unit + same regime/profile/choices -> normalize twice | Deterministic recomputation | Same canonical graph and claimed semantic IDs; no admission follows merely from agreement |
| Candidate -> authenticate twice with same exact closure | Independent recomputation | Same authentication result; normalizer witness need not be trusted |
| Authenticated -> admit twice under same exact normative regime | Deterministic recheck or shared checked basis | Same semantic admission outcome; process-local handles need not be object-identical |
| Admitted -> persist | Representation production | Bytes name the same semantic subject; they do not contain the admitted capability |
| Bytes -> decode | Transport reconstruction | Immutable carrier only; no dependency or semantic admission claim |
| Decoded -> authenticate | Independent semantic identity reconstruction | Same IDs only if physical normal form, regime, and complete dependency closure check |
| Authenticated -> admit in a new process | Whole-Protocol re-admission | New process-local capability; no continuity from producer process |
| Copy opaque admitted handle in one process | Capability sharing | Same authority may be preserved because immutable private storage is shared |
| Serialize or print an admitted handle | Capability destruction at representation boundary | Recipient receives raw data and must decode/authenticate/admit |
| Reopen -> no edit -> same normalization inputs | Deterministic canonical recovery | Same semantic ID is expected; authority is nevertheless reconstructed, not inherited |
| Reopen -> semantic edit or new regime | New subject construction | New Core/Protocol ID as applicable and mandatory re-admission |
| Same canonical Protocol under two transport encodings | Representation equality after authentication | Same Protocol ID may coexist with different bytes/transport digests |
| Same bytes presented under a different expected semantic regime | No reinterpretive replay | Authentication refuses; a regime change cannot silently preserve identity |
| Same resolver with an uncited addition | Closure-independence replay | Resolution/authentication/admission result must remain unchanged |
| Same cited ID with changed preimage | No valid replay | Authentication refuses mismatch; absence of a required preimage is `CannotAnswer` |
| Persisted artifact from a newer unsupported transport schema | No implicit upgrade | Decode returns `Unsupported`; exact-v0 does not guess or normalize historical bytes |
| Source-free consumer view or OIR | Local validation only | It may establish local facts but cannot replay source-relative coverage |
| Checked successor proposal | Validator replay, not search replay | Checker reconstructs the named predecessor/successor relation from exact inputs; producer search remains untrusted |

“Replay” must always name which of deterministic recomputation, independent
validation, re-authentication, certificate verification, or observational
reproduction is meant. This lifecycle selects direct recomputation and
re-admission for canonical Protocol artifacts; it does not propose a universal
transition record.

### 11.1 Residual trust and independent checkability

- Authors, importers, generators, normalizers, linkers, composers, and compiler
  search procedures are proposal producers. Canonical authentication and
  admission do not trust their claimed success or search history.
- The carrier decoder is trusted to form bounded immutable in-process data
  safely. Its successful result is intentionally weaker than semantic
  authentication.
- Authentication relies on the exact canonical grammar and encoder,
  dependency decoders, content-identity primitive, and regime dispatch. An
  independent implementation can check the same result without reproducing
  normalization search.
- Admission relies on the normative checker for the exact semantic regime.
  Multiple checker implementations may reduce implementation reliance, but
  agreement does not silently strengthen the semantic claim.
- A source-to-canonical witness, import correspondence, checked-transform
  relation, or projection certificate is trusted only through its own named
  checker. Protocol admission does not absorb any of those claims.
- Capability use relies on opaque interfaces and immutable storage. Any API
  exposing a mutable carrier changes the result type to raw input rather than
  extending the capability contract.
- Persistence relies on atomic publication for its operational guarantee.
  Recipients rely on their own decode, authentication, and admission, not on
  the producer's release marker or API discipline.
- A consumer-view adapter is part of the named consumer's checking boundary.
  If independent validation is required, the view must expose sufficient
  source-bound inputs or become a separately checked domain artifact.

## 12. Refusal matrix

The matrix names the highest-level outcome class. Stable diagnostic subcodes
belong to the owning transition and may be more precise.

| Transition | Malformed | Unsupported | Unauthenticated | Inadmissible | Refused | Cannot answer / operational rule |
|---|---|---|---|---|---|---|
| `Author` | Source cannot form workbench syntax | Unknown authoring construct/profile | — | — | Explicit authoring constraint false | Missing input is `CannotAnswer`; no `AuthoringUnit` |
| `Import` | External representation malformed | Source language/version or feature outside importer | Source authenticity mismatch only if importer promises to check it | — | No defined import mapping for a well-formed construct | Missing importer dependency or source snapshot is `CannotAnswer`; no partial target |
| `Resolve` | Ill-formed reference syntax | Dependency schema unsupported | Supplied content does not match a cited digest, if already claimed | — | Missing/ambiguous/cyclic/incompatible named resolution under available snapshot | Unavailable resolver material is `CannotAnswer`; no partial resolved subject |
| `Normalize` | Resolved state violates its formation invariant | No canonical lowering for a workbench construct | — | — | Required schedule/interpretation/choice cannot be selected or information-loss precondition fails | Internal/resource failure is `CannotAnswer`; candidate and typed side outputs commit together |
| `Authenticate` | Carrier cannot form closed PIR source type | Unknown canonical op/schema/regime encoding | Noncanonical form, dependency mismatch, identity mismatch, undeclared field, or expected-ID mismatch | — | — | Missing dependency preimage/checker is `CannotAnswer`; no authenticated handle |
| `Admit` | Impossible through public authenticated type; raw ingress authenticates first | Normative regime checker not implemented | Impossible if authenticated input remains immutable | Whole-Protocol predicate is false | — | Checker/resource unavailable is `CannotAnswer`; no admitted handle |
| `PersistProtocol` | Impossible through admitted capability API | Transport schema not writable | — | — | Policy may refuse a destination without changing admission | I/O failure is operational; publish atomically or remove incomplete output |
| `Decode` | Bad framing, resource bounds, root shape, or carrier parse | Unknown transport/dialect version | Transport digest mismatch may be named here; semantic mismatch yields no authenticated result | — | Optional transport selector mismatch | I/O unavailable is operational; no decoded handle |
| `DeriveView` | Impossible through typed admitted source; malformed auxiliary subject refused at its owner | Question, target, or source construct outside view schema | Auxiliary subject ID/source binding mismatch | — | Well-formed source does not satisfy view-specific precondition | Missing theorem/interface/plan/authority is `CannotAnswer`; a negative analysis may be successful `NegativeJudgment` |
| `Reopen` | Impossible through typed capability | — | — | — | — | Allocation/resource failure only; original capability remains valid |
| `LinkAuthoringUnits` | Link plan or source authoring shape malformed | Link construct/face mode unsupported | — | — | Ambiguous face, incompatible seam, namespace, schedule, or dependency condition | Missing explicit resolution input is `CannotAnswer`; inputs unchanged and no partial output |
| `ComposeAdmittedProtocols` | Composition plan malformed | Composition mode or child feature unsupported | Child capabilities are already admitted; explicit Interface binding may mismatch | Composite candidate is not yet admitted here | Causal/challenge/failure/face plan cannot define one composite | Missing seam authority is `CannotAnswer`; no child authority is consumed or invalidated |
| Checked successor | Proposal carrier malformed | Transform family/relation unsupported | Successor identity or predecessor binding mismatch | Successor fails admission | Named predecessor/successor relation is false | Search/checker/resource failure is `CannotAnswer`; predecessor remains valid |

Every semantic boundary is transactional with respect to authority: a failed
transition may return diagnostics, counterexamples, or an explicitly
unauthoritative proposal, but never a partially authenticated/admitted
capability. Operational systems with unavoidable external partial effects must
report those effects in a different result type rather than reuse this
lifecycle rule.

## 13. Scenario pressure tests and falsifiers

### 13.1 Equivalent authoring representatives

Two authoring units differ only in labels, redundant defaults, and order proved
irrelevant to all protected observers. They resolve under the same closure and
normalize under the same profile.

Expected result: one physical canonical graph and one `ProtocolId`, not two
sealed carrier representatives whose equality exists only in the encoder.
Authentication rejects either noncanonical spelling even if a quotient encoder
could compute the same hash.

Falsifier: a Stage 3 semantic field cannot be represented in the unique graph
without retaining arbitrary source form. That would reopen the canonical-level
decision or require the field to move to Interface, Plan, or provenance.

### 13.2 Resolver closure independence

One resolver snapshot adds an uncited entry; another changes a cited preimage.

Expected result: the uncited addition has no semantic effect. The changed
preimage refuses authentication or yields a deliberately new candidate and ID;
it cannot silently re-admit the old ID.

Falsifier: a normative result changes with an uncited resolver addition. The
read set is then incomplete or the dependency manifest is not closed.

### 13.3 Cross-process artifact use

An admitted Protocol is persisted and loaded by a fresh process.

Expected result: transport decode, semantic authentication, and admission are
three distinguishable claims. The receiving process gets a new capability only
after all required checks. Producer-side admitted-only persistence reduces
accidental distribution of candidates but is not trusted by the receiver.

Falsifier for admitted-only official persistence: a concrete supported
cross-process workflow must exchange canonical candidates before admission and
cannot use a distinctly typed unauthoritative cache/envelope. Until such a
consumer exists, admitting raw candidates to the official artifact kind is an
avoidable grade ambiguity.

### 13.4 One Protocol, two Interfaces or Plans

Two external ABIs or two prover strategies depend on one Protocol.

Expected result: Protocol authentication and admission are reusable. A
consumer whose answer depends on ABI labels receives `ProtocolInterfaceId`; a
plan-sensitive consumer receives `ProverPlanId`. Neither reads unidentified
carrier metadata.

Falsifier: two views over equal advertised inputs and equal IDs return
different semantic answers because of hidden carrier labels, retained
resolver entries, or plan state.

### 13.5 No-op reopen and real change

One reopened branch is unchanged; another changes a protected observation.

Expected result: both are raw. The no-op branch may recover the original ID
after normalization; the changed branch receives a new ID. Both re-authenticate
and re-admit. The source capability remains valid.

Falsifier: a mutable branch continues using the source capability, or an old
ID remains authoritative before independent authentication.

### 13.6 Repeated-child composition

The same admitted child Protocol occurs twice in a composite.

Expected result: two occurrence namespaces, explicit seams and interleaving,
one new Core candidate, and whole-composite admission. Child IDs and authority
are input facts, never output authority.

Falsifier: the composition result inherits a child identity/admission or lets
the same child occurrence alias transcript, failure, claim, or port state
without an explicit composition rule.

### 13.7 Source-free derived artifact

A consumer sees only OIR or a serialized view.

Expected result: it may authenticate and validate that subject under its own
schema. Source-relative completeness or projection coverage is
`CannotAnswer` without admitted source authority or sufficient source-bound
evidence.

Falsifier: a source-free target claims to prove absence of omitted source
obligations using information not present in its inputs.

### 13.8 Regime and transport evolution

The carrier bytes remain identical while a semantic regime changes, or the
semantic subject remains identical while the transport changes.

Expected result: a regime change cannot preserve semantic identity by
accident. A transport change may preserve semantic identity only after exact
decode and authentication under the same semantic regime.

Falsifier: decoder success is treated as a semantic migration proof or an
unsupported historical schema is silently upgraded into a current candidate.

## 14. Unresolved choices and working defaults

| Choice | Working default | Why it is not yet final | Reversal evidence |
|---|---|---|---|
| Logical split between authentication and admission | Keep distinct result types and refusal classes; allow a fused implementation traversal | Stage 3 must assign every formation and whole-semantic predicate to exactly one side | A predicate cannot be placed without either circular authority or repeated semantic interpretation, and no claim-preserving factoring exists |
| Official artifact writer input grade | `AdmittedProtocol` only; candidate caches use a separate envelope | No current target consumer requires canonical pre-admission interchange | A named workflow needs it and the separate cache type cannot satisfy replay or collaboration requirements |
| Claimed IDs stored in the candidate | Permit stored claims for interchange, always independently recompute | Exact canonical grammar and envelope remain Stage 3 work | A computed-only representation is simpler for every named consumer and preserves useful expected-ID selection |
| `ResolutionClosure` persistence | Process-local immutable record; optional provenance/cache form, no universal environment ID | Import auditing and distributed authoring requirements are not yet known | A named independent normalizer must reproduce resolution from a durable exact snapshot |
| Admission basis retention | Minimal exact regime and dependency closure, not the whole resolver | Consumer read-set integration is still in progress | A normative consumer repeatedly needs material that cannot be typed as its own explicit input and truly belongs to Protocol admission |
| Normalization witness | Optional; never trusted for target authentication/admission | Source correspondence and audited import may need stronger evidence | A named independent source consumer requires checked source-to-canonical correspondence |
| Static composition entry point | Keep authoring link and admitted semantic composition as different operations | Exact composition algebra is Stage 3 work | One contract can express both without grade ambiguity, ambient reads, or inherited authority |
| Child IDs in composite Core preimage | Defer exact encoding; require a new Core ID either way | Stage 1 fixed the semantic result, not its canonical composition encoding | Stage 3 composition semantics show whether inlining or explicit child references is the complete canonical invariant |
| Capability copy/thread semantics | Require opacity and immutable sharing semantically; leave language mechanics to implementation | Rust/C++ and future checker processes express this differently | A language-neutral portable capability model becomes a real cross-process requirement |
| Serialized admission receipt | Do not introduce one in v0 | Consumers can rerun bounded admission and no independent receipt consumer is named | Admission becomes too costly or unavailable for a named consumer with an explicit trust/checker model |
| Transport compatibility window | Exact-v0 fail closed; no implicit upgrades | No declared retention window or independent release cadence yet exists | A deployment promises long-lived artifacts or independent producer/consumer releases |
| Durable consumer views | Ephemeral by default; promote only for a named cross-process consumer | A universal fact root remains rejected | A specific view requires independent exchange, caching, and validation with a stable owner |
| Expected `ProtocolId` check placement | Conceptually authentication; decode may reject early without strengthening its result | APIs may optimize error locality and resource use | Early checking becomes the only identity check or causes decode to imply missing dependency authority |

## 15. Provisional conclusions

The strongest lifecycle hypothesis is a capability-centric spine with
domain-owned semantic bridges:

1. authoring and import produce only proposals;
2. resolution closes environmental reads and normalization deterministically
   creates the one physical canonical candidate;
3. authentication establishes exact identity and dependency closure;
4. admission establishes the whole-Protocol predicate and mints process-local
   authority;
5. official persistence consumes admitted authority but never serializes it;
6. decoding reconstructs a carrier, after which authentication and admission
   repeat independently;
7. views narrow authority to explicit consumer questions and auxiliary
   subjects;
8. reopening creates a raw branch without revoking the source; and
9. link, composition, and checked change always produce a new candidate whose
   authority must be reconstructed.

This model retains the strongest current implementation properties—fail-closed
boundaries, opaque immutable handles, cited dependency closure, transactional
linking, and explicit re-admission—while making the Stage 1 authoring/canonical
split real and eliminating ambient carrier and resolver reads from target
consumer contracts.

Before convergence, the other Stage 2 workstreams must test this spine against:

- the exact semantic-bridge relation catalog;
- Interface and ProverPlan consumption at Analysis, Compiler, and OIR seams;
- endpoint projection and source-bound coverage;
- realization, operational effects, Evidence, and reliance boundaries;
- external checking and certificate cases; and
- equal-resolution candidate comparison.

## 16. Research basis

### Current zkc sources

- [Boundary specification](../../../docs/spec/boundaries.md)
- [Carrier and artifact specification](../../../docs/spec/carrier.md)
- [Versioning specification](../../../docs/spec/versioning.md)
- [Kernel specification](../../../docs/spec/kernel.md)
- [Compiler specification](../../../docs/spec/compiler.md)
- [Artifact API](../../../include/zkc/Artifact/Artifact.h) and
  [implementation](../../../lib/Artifact/Artifact.cpp)
- [Seal engine](../../../lib/Semantics/SealEngine.cpp)
- [Link engine](../../../lib/Semantics/LinkEngine.cpp)
- [In-memory artifact boundaries](../../../lib/Dialect/Pir/Transforms/ProtocolArtifacts.cpp)
- [Artifact lifecycle test](../../../test/lib/TestArtifactLifecycle.cpp)
- [Fail-closed artifact tests](../../../test/Artifact/fail-closed.test)
- [Encoding normalization tests](../../../test/Encoding/normalization.mlir)

### External primary sources

- [MLIR Dialect Conversion](https://mlir.llvm.org/docs/DialectConversion/)
- [MLIR Canonicalization](https://mlir.llvm.org/docs/Canonicalization/)
- [MLIR Bytecode Format](https://mlir.llvm.org/docs/BytecodeFormat/)
- [RFC 6920: Naming Things with Hashes](https://datatracker.ietf.org/doc/rfc6920/)
