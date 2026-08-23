# Stage 3 integrated scenario and falsification results

> **Document kind:** Temporary integrated validation record
> **Document state:** Stage 3.3 scenario pass complete against the frozen target
> model and equal-resolution Candidate A--E portfolio; convergence input, not a
> design decision
> **Authority:** None. These are symbolic model evaluations. They do not
> admit a Protocol, validate an implementation, execute a proof system, or
> establish a cryptographic property.
> **Evaluated model:**
> [`target-semantic-model.md`](target-semantic-model.md)
> at frozen SHA-256
> `107255938efa6af7802030b93bdbc9dcb4d5535335866cffa304df33083a7f5b`
> **Candidate context:** [`candidate-models.md`](candidate-models.md)
> **Disposition:** Preserve accepted scenario obligations and decisive
> falsifiers in durable owners, then remove this temporary record at cutover.

## 1. Evaluation method and result

This record instantiates every scenario required by the
[`Stage 3 entry contract`](../stage-2-transitions/stage-3-entry-contract.md#8-required-scenarios-and-validation).
The evaluation is semantic rather than empirical: each trace supplies exact
immutable inputs to the model's named operation, follows the declared
authentication, admission, or relation boundary, and checks whether the
required qualified result follows without an ambient read or forbidden
inference.

The model-level result is:

| Family | Cases | Result |
|---|---|---|
| Protocol identity and admission | `P1`--`P3` | Pass |
| Interface | `I1`--`I2` | Pass |
| Relations | `L1`--`L3` | Pass |
| Plan and realization seam | `R1` | Passes the partition law under an explicit hypothetical observer; production classification remains a Stage 4B result |
| Fiat--Shamir | `F1`--`F2` | Pass; property conclusions remain intentionally unavailable without later-owned bases |
| Composition | `C1`--`C2` | Pass |
| Structural versus property relation | `T1` | Pass |
| Persistence and capability | `S1` | Pass |
| OIR source coverage | `O1` | Pass at the ownership seam; Stage 3 does not claim an OIR-local result |

`R1`, `F2`, and `O1` pass because the exact required result includes a bounded
later-owned answer or `CannotAnswer`; inventing an affirmative Stage 3 result
would fail those scenarios. No blocking contradiction remains in the
frozen evaluated model. Several schema defects found during the first pass were
corrected before this record was synchronized: authoring normalization now has an
explicit audit; composition uses local child/target references, complete
ordinary/terminal origin maps, exhaustive declaration provenance, complete
challenge/private-randomness bundles, total failure/reach-exit policies,
result-routed static terminals, and target admission before result authority;
relation profiles, adapters, observations, comparisons, and correspondence
questions are distinct; FS construction is a separate carrier dependency with
exact transcript actions; and Plan classification no longer self-authorizes
before OIR exists.

No code or bounded feasibility artifact was created, so no implementation test
result is claimed.

## 2. Shared notation and fixtures

### 2.1 Qualified outcomes

The traces use the model's exact outcome classes:

```text
Affirmative
Negative(reason, retained_facts)
Unsupported(exact construct or question)
CannotAnswer(missing named semantic input or basis)
Refused(missing authority or prohibited invocation)
Malformed(exact framing or structural defect)
CheckerFailure(operational failure; no semantic conclusion)
```

An `Affirmative` or `Negative` result is a completed semantic check. The other
classes do not refute the checked proposition. `cap(X)` denotes an opaque,
immutable, process-local capability for exact subject or result `X`; an ID or
serialized record is never shorthand for that capability.

### 2.2 Exact fixture roots

Unless a scenario overrides one field, it holds these inputs fixed:

- `rhoP`, `rhoI`, `rhoPlan`, `rhoRI`, `rhoRX`, `rhoRB`, `rhoRAP`,
  `rhoRAD`, `rhoRAO`, `rhoCorr`, and `rhoComp` are exact Protocol, Interface,
  Plan, relation-interface, relation-instance, relation-binding,
  artifact-profile, relation-adapter, artifact-observation, correspondence,
  and composition regimes;
- `Delta` is the least authenticated dependency-preimage graph for the
  subject under test;
- `C` is a finite admissible InteractiveCore with one exactly-one public
  statement input port, one exactly-one private witness input port, one prover
  obligation and its exact nonproduction-failure family, at least one proof
  message, one fresh public
  challenge, one check, explicit reject/abort paths, and one fallback terminal;
- `PF = (C, FreshPublicCoins)`, with semantic IDs `c = CoreId(C)` and
  `pF = ProtocolId(PF)` and local authorities `cap(PF)` and
  `core_view(PF)` after admission;
- `I` is an admitted lossless Interface for `PF`;
- `RI` is an admitted relation interface, `RB` is an admitted binding from
  `I` to `RI`, and all adapters cited below are exact admitted adapters; and
- each checker receives its owner-defined narrow view, exact regime, exact
  dependency closure, and exact operation inputs. There is no implicit
  default registry or current-context object.

The fixtures are schematic mathematical values, not claims about a particular
repository artifact or protocol family.

## 3. Protocol identity and admission

### P1 — authoring quotient versus protected observation

**Status:** Pass.

**Declared immutable inputs.** Let `N` be one exact
`AuthoringNormalizerContract` with finite quotient rules for hygienic local
renaming and a fully checked macro expansion. Let `A0` use an inline form and
human label `left`; let `A1` use the declared macro form and an alpha-renamed
label. Their resolved read-closure snapshot is the same `Delta`. Let `A2` equal
`A0` except that one proof-message event removes its `Transcript` protected
observation while retaining its `Wire` observation. All three calls use `N`,
`Delta`, and `rhoP`.
For the shared normalized candidate `P0` and changed candidate `C2`, fix their
exact Fresh authentication bundles `B0` and `B2`, matching dependency-
authentication records
`Adep0 = {core = exact same-key map as B0.core_dependencies,
transcript = None}` and
`Adep2 = {core = exact same-key map as B2.core_dependencies,
transcript = None}`, resulting retained Protocol dependency views `V0` and
`V2`, and exact admission-checker bundles
`L0 = {core = Lcore0, transcript = None}` and
`L2 = {core = Lcore2, transcript = None}`. Both admission calls use
`NoCompositionContext`; an extra transcript checker is not permitted for a
Fresh Protocol.

**Initial subject and authority state.** `A0`, `A1`, and `A2` are authoring
material only. None has a semantic ID, authenticated candidate, or admission
capability.

**Operation and exact result.** Run:

```text
NormalizeAuthoring(Ai, Delta, N, rhoP)
  -> Qualified(candidate_i: CanonicalProtocolCandidate,
               interface_candidates_i,
               prover_plan_candidates_i,
               audit_i: NormalizationAudit<ProtocolAuthoring>)
```

Both typed candidate sequences are empty in this fixture.
`audit_0` and `audit_1` record the spelling and declared expansion differences
as quotient-neutral after their pre-erasure checks. Both operations return the
same canonical Protocol candidate `P0`. Encoding and canonical PIR
authentication use
`B0 = {core_dependencies = every and only member of P0's least Core
dependency closure, transcript_construction = None}` and `Adep0`. Each equal
candidate then runs
`AdmitProtocol(authenticated P0, V0, NoCompositionContext, L0)`. Both paths
recompute the same `CoreId` and `ProtocolId` and mint equivalent fresh local
admission capabilities. The changed candidate is likewise authenticated with
`B2` and `Adep2`, then admitted with
`AdmitProtocol(authenticated C2, V2, NoCompositionContext, L2)`.

`audit_2` cannot classify the changed transcript observation as neutral. Let
`C0` be `P0`'s canonical Core. In this instantiation the audit retains the
changed observation in `C2`; authentication
with its own exact Fresh dependency bundle therefore computes
`CoreId(C2) != CoreId(C0)` and a different `ProtocolId`.
Refusal before erasure would also satisfy the contract, but silent erasure
would not.

**Identity effects.** `A0` and `A1` converge only under the exact finite
quotient in `N`; `A2` has a different semantic identity. Equality is not
inferred across another normalizer contract or semantic regime.

**Capability and replay effects.** Normalization mints no authority. Each
candidate is independently authenticated and admitted. A new process must
re-supply `N`, `Delta`, authoring input, and audit inputs to replay the
normalization claim, or authenticate the canonical Protocol directly without
claiming anything about its absent source.

**Preserved nonclaims.** Same Protocol identity is not general behavioral
equivalence, source provenance, faithful macro provenance, or a proof that an
arbitrary front end preserved information.

**Decisive falsifier.** `A2` receives the same Protocol ID after the protected
change, or either equal-ID result depends on an undeclared resolver, policy,
or pre-erasure choice.

### P2 — transport equality cannot erase regime

**Status:** Pass.

**Declared immutable inputs.** `b` is a transport encoding that decodes to the
one physically canonical PIR graph `G` for `PF`. The graph claims `rhoP` and
`pF`. `rhoP2` is a distinct Protocol semantic regime. `Delta` is the exact map
containing every and only dependency preimage in `G`'s least Core dependency
closure. Hold fixed
`Bfresh = {core_dependencies = Delta, transcript_construction = None}` and the
exact matching dependency-authentication record
`Adep = {core = exact same-key map as Bfresh.core_dependencies,
transcript = None}` is supplied across the regime substitution.
For the same-regime success path, also fix the resulting retained dependency
views `Vfresh` and exact checker bundle
`Lfresh = {core = LcoreFresh, transcript = None}`; admission uses
`NoCompositionContext`.

**Initial subject and authority state.** The caller has bytes and dependency
preimages but no authenticated or admitted capability.

**Operation and exact result.**
`AuthenticateCanonicalPir_rhoP(b, Bfresh, Adep)` transport-decodes to `G` and
first permits only
`ReadUnchecked_rhoP`; dependency-preimage authentication and ID recomputation
then establish the ID-consistent canonical graph predicate, after which
`Read_rhoP` is exposed and authentication returns
`Affirmative(AuthenticatedCanonicalProtocolCandidate GP)` retaining recomputed
ID `pF` and exact views `Vfresh`.
`AdmitProtocol(GP, Vfresh, NoCompositionContext, Lfresh)` then
mints the local `AdmittedProtocol` capability. Fresh admission refuses a
missing Core checker or an extra transcript checker.
`AuthenticateCanonicalPir_rhoP2(b, Bfresh, Adep)` is instead a successful negative
with `RegimeMismatch(rhoP, rhoP2)` before admission. If a
different profile intentionally re-encodes the semantic fields under
`rhoP2`, its identity preimage contains `rhoP2` and cannot equal `pF` merely
because some payload bytes happen to match.

**Identity effects.** Same-regime transport replay reconstructs `pF`; regime
substitution returns `Negative(RegimeMismatch)` for the claimed root or, after
explicit re-encoding in the new regime, computes a regime-separated identity.
Byte equality never preserves identity across the substitution.

**Capability and replay effects.** Same-regime authentication still produces
only an authenticated candidate; the exact four-input `AdmitProtocol` call
must run locally. Neither the bytes nor `pF` cross as `cap(PF)`.

**Preserved nonclaims.** The result does not show compatibility or semantic
equivalence between `rhoP` and `rhoP2`.

**Decisive falsifier.** One raw graph authenticates to the same Protocol ID
under both distinct semantic regimes, or the checker silently adopts the
embedded regime while reporting that it checked `rhoP2`.

### P3 — physical authentication and whole-Protocol admission

**Status:** Pass.

**Declared immutable inputs.** `Gclosure` is a physically canonical graph with
typed, in-bounds references and recomputable IDs, but one exact
port-occurrence-derived message input is not available to its acting role on
that guard path at that schedule point. `Gphysical` is parseable
MLIR with the same intended fields but a noncanonical operation-group order
and an omitted explicit default. Each has its exact claimed regime and
dependency inputs.

Also fix four physically canonical one-field variants of an otherwise
admissible Core: `GmalformedAbort` makes a `MalformedProtocolInput` failure
terminate at `Abort`; `GcheckAccept` makes `CheckRejected` terminate at
`Accept`; `GsamplingReject` makes `ChallengeSamplingFailed` terminate at
`Reject`; and `GexplicitContinue` gives `ExplicitProtocolAbort` a
`ContinueWithStatus` effect. Their failure sources and backlinks are otherwise
exact. Each variant has its own exact Fresh preimage bundle, same-key
`{core, transcript = None}` authentication-capability record, retained views,
and `{core, transcript = None}` admission-checker record.

Fix exact Fresh authentication bundles `Bclosure` and
`Bphysical`, each with `core_dependencies` equal to every and only member of
that graph's intended least Core dependency closure and
`transcript_construction = None`. Fix their exact matching
dependency-authentication records `AdepClosure` and
`AdepPhysical`, each exactly
`{core = same-key map as the corresponding B*.core_dependencies,
transcript = None}`.
For `Gclosure`, fix the resulting retained views `Vclosure` and exact Fresh
admission checker bundle
`Lclosure = {core = LcoreClosure, transcript = None}`; use
`NoCompositionContext`.

**Initial subject and authority state.** Every candidate is raw carrier
material. None has authentication or admission authority.

**Operation and exact result.**
`AuthenticateCanonicalPir_rhoP(Gclosure, Bclosure, AdepClosure)` is affirmative
and returns an immutable authenticated candidate. Its subsequent
`AdmitProtocol(authenticated Gclosure, Vclosure, NoCompositionContext,
Lclosure)` is
`Negative(RoleKnowledgeUnavailable(event, value))`. In contrast,
`AuthenticateCanonicalPir_rhoP(Gphysical, Bphysical, AdepPhysical)` is
`Negative(PhysicalCanonicalityViolation(group_order, explicit_default))`
before a semantic candidate can be admitted.
Each of the four failure/terminal variants authenticates successfully under
its own exact inputs but its four-input `AdmitProtocol` call returns a
successful `Negative` at whole-Protocol admission. The retained reasons are,
respectively, the exact violated equations
`MalformedProtocolInput -> Reject`, `CheckRejected -> Reject`,
`ChallengeSamplingFailed -> Abort`, and
`ExplicitProtocolAbort -> Terminate(Abort)`. In particular, no terminating
failure may select `Accept`, and the event spelled `RaiseFailure` cannot make
an explicit abort catchable by assigning a continuing status.

**Identity effects.** The authenticated but inadmissible candidate can have a
recomputed claimed semantic ID; that ID has no admission authority. The
physically noncanonical input has no authenticated semantic subject. Each
failure/effect or failure/terminal substitution is identity-bearing, but its
recomputed ID does not license the inadmissible combination.

**Capability and replay effects.** The first trace may retain an authenticated
candidate handle for diagnostics but mints no `AdmittedProtocol`; the four
failure-compatibility traces have the same authority disposition. The
physically noncanonical trace mints neither authentication nor admission
authority. Reopening any input reruns the respective boundary. A
missing Core checker, extra transcript checker for Fresh, or checker scoped to
another dependency is refused rather than inferred.

**Preserved nonclaims.** Physical canonicality does not prove Core closure;
Core closure does not prove relation truth or any cryptographic property.
`MalformedProtocolInput` here is a decoded Protocol-level semantic class, not
an Interface byte-decoding failure.

**Decisive falsifier.** One combined `valid` bit obscures which boundary
failed; an incompatible class/effect/result combination passes admission or
is misreported as carrier malformedness; an explicit abort is captured or
continued; or any failure mints or deserializes admission authority.

## 4. Interface

### I1 — multiple lossless Interfaces over one Protocol

**Status:** Pass.

**Declared immutable inputs.** `Ialpha` and `Ibeta` both depend on `pF`.
`Ialpha` exposes names `statement` and `proof`; its statement-binding
`encode`/`decode` pair directly owns one length-delimited statement-container
byte language, and its proof binding's `encode_active_trace`/`decode_bytes`
pair directly owns one length-delimited proof-container byte language.
`Ibeta` exposes names `public_input` and `argument`; the corresponding two
named function pairs directly own different total injective encodings and
total tagged decoders. There is no inner semantic codec plus independently
variable outer wrapper in either Interface. For the sole public `Statement`
input occurrence, `Ialpha.statement` and `Ibeta.public_input` each use
`representation = StatementContainerMember`, carry no
`IndependentValueCodec`, and their respective statement-binding shapes are
`OneToOne(StatementExternalOccurrenceRef(the exact external port, 0))`. Every
other external port uses its own
`IndependentValueCodec(LosslessContainerCodec)` with a directly checked
round-trip law. Both Interfaces round-trip to the same one canonical statement
assignment
`ProtocolPublicAssignment<pF> = {protocol_id = pF, values = the total map over
every and only ProtocolPublicStatementOccurrenceRef in PF}` and the same
complete action-occurring proof-channel message trace (not the Core
`ProverTrace`). Every assigned value is canonical in its exact referenced port
domain; neither decoder can produce a wrong-Protocol, partial, extra-
occurrence, wrong-occurrence, or wrong-domain assignment. Both preserve the
same external port domains/directions, exact
Protocol-port multiplicities, and role entries. Each statement binding covers
every occurrence of every public `Statement` input exactly once, with no
ordinal omission or alias. Both bind every and only
Proof-channel message through a potential-position bijection whose presence
entry is exactly
`ProofEventOccurrencePredicateRef = EventActionOccurrence(message_event)`,
denoting that event's Core `EventActionOccurs` predicate, using the corresponding
`AlwaysOccurs`, unambiguous `OmittedWhenNotOccurs`, or explicit-nonoccurrence-tag
form, and preserve the exact action-occurring realized schedule subsequence.
Their decoders
reconstruct the guarded potential-position trace without running the verifier.
Both give every Core terminal one distinct external tag whose payload binding is
exactly that terminal's ordered public outputs under a lossless tuple codec. A
terminating failure is represented only through its effect terminal; a
continuing failure has no external outcome tag, and `ProverDidNotProduce`
remains a separate producer-trace outcome. They reconstruct the same canonical
ports, message occurrences, and terminal outcomes without restriction or
default. `RBalpha` and
`RBbeta` are separate
relation bindings dependent on the respective Interface IDs. Both
map every and only `RI` public/witness occurrence to the same allowed exact
`PF` statement/private-Prover occurrence with total two-sided-round-trip value
bridges, carry the same kind-correct exact claim/check/Accept-terminal result
reference, and have empty committed-object grounding maps. Both
correspondence calls fix
`QI = {base_clauses = {PublicPorts, WitnessPorts,
ResultBindingReferenceShape}, artifact_question = None}` and no artifact comparison or
committed-object grounding input.

For each Interface `Ix`, `Ix.algorithm_dependencies` maps every
`ContentAddressedContractRef` reachable from any Interface codec, encoder, or
decoder—including every external-port `IndependentValueCodec`, every
external-outcome `payload_codec`, statement `encode`/`decode`, and proof
`encode_active_trace`/`decode_bytes`—to exactly one kind-, regime-, content-,
and ABI-matched declaration. It is exactly the least reachable closure; a
closed finite term has no map entry.
Fix `Bx` as its exact `ExactInterfaceDependencyPreimageBundle`, `Ax` as the
exact matching dependency-authentication capability bundle, `Vx` as the
resulting retained dependency views, and `Lx` as the exact identity-matched
`ExactInterfaceLawCheckerCapabilities`, separately for `Ialpha` and `Ibeta`.
For each dependent `RBx`, fix `DBx` as the every-and-only least closure of its
value-bridge algorithms keyed by full
`TypedRelationBindingAlgorithmDependencyRef`, `ABx` as matching dependency-
authentication capabilities, `VBx` as resulting retained views, and `LBx` as
exact binding-law checker capabilities. This fixture has no committed-object
grounding entry, so the exact admitted-adapter-view input is empty.

**Initial subject and authority state.** `cap(PF)` exists. Both Interface and
binding values begin without admission authority. Each exact `Bx`, `Ax`, and
`Lx`, `DBx`, `ABx`, and `LBx` is available as an operation input, but no `Vx`,
`VBx`, Interface capability, or binding capability exists before its owning
authentication.

**Operation and exact result.** For each `Ix`,
`AuthenticateProtocolInterface(Ix, Bx, Ax)` is affirmative, followed by
`AdmitProtocolInterface(authenticated Ix, exact PF view, Vx, Lx)`.
Interface admission is affirmative for both subjects because their codecs are
total and lossless and neither changes Protocol trace semantics. A missing,
extra, aliased, kind/regime/content/ABI-mismatched dependency entry, preimage,
retained view, authentication capability, or law-checker capability is
refused or fails its owning boundary; it cannot be ambiently filled. Their
respective calls
`AuthenticateRelationBinding(RBx, DBx, ABx)` and
`AdmitRelationBinding(authenticated RBx, exact PF binding view, Ix, RI, VBx,
{}, LBx)` are then affirmative. The admitted bindings yield separate
affirmative
`RelationCorrespondsAtInterface(PF, Ix, RI, RBx, QI, None, None, rhoCorr)` results,
`CheckedRelationCorrespondenceJudgment CIalpha` and
`CheckedRelationCorrespondenceJudgment CIbeta`, over the same requested
Protocol facts. The exact admitted Protocol capability and
its attenuated Core view remain reusable because neither depends on an
Interface; no
transaction-scoped Core-admission witness is exported or reused. A later
projection request must name `ProtocolInterfaceId(Ialpha)` or
`ProtocolInterfaceId(Ibeta)` exactly.

**Identity effects.** `pF` is unchanged, while
`ProtocolInterfaceId(Ialpha) != ProtocolInterfaceId(Ibeta)`. The binding IDs
also differ because their dependent Interface IDs differ.

**Capability and replay effects.** An admitted `Ialpha` capability cannot be
relabelled as `Ibeta`. Passing `RBalpha` with `Ibeta` yields a dependency
mismatch rather than a `CheckedRelationCorrespondenceJudgment`. Neither
`CIalpha` nor `CIbeta` can be widened to the other Interface. Every process
reauthenticates the exact
chosen Interface dependency closure with its local matching capabilities,
retains new attenuated dependency views, and re-admits that Interface and its
binding after separately reauthenticating `DBx` with new `ABx`, retaining new
`VBx`, and reacquiring `LBx`.

**Preserved nonclaims.** Two lossless Interfaces are not thereby identical in
application ergonomics, deployment behavior, cost, or policy acceptance.
Interface decoding forms only the public-`Statement` assignment subset and
proof-message payload occurrences. It neither forms the remaining
`CoreInvocationInputs`, decomposes arbitrary message payloads into
prover-obligation outputs, chooses private inputs, nor constructs a
`RandomnessReplay`. A nonterminal external output port fixes only a typed value
grouping and lossless representation; it creates no Core exposure occurrence
or path-availability fact. Stage 4B must bind its OIR exposure and prove exact
availability and visibility. Terminal payload exposure remains exactly the
separate `external_outcomes` semantics.

**Decisive falsifier.** Changing an Interface changes `pF`, a consumer reads an
ambient “current Interface,” or one Interface-dependent result is accepted
under the other ID; or dependency preimages, views, and checker capabilities
are inferred from IDs or an ambient registry.

### I2 — semantic restriction, default, and transcript rewrite

**Status:** Pass.

**Declared immutable inputs.** Three physically well-formed Interface
candidates depend on `pF`: `Jrestrict` rejects one canonical statement value
accepted by `PF`; `Jdefault` accepts an absent external field by injecting a
semantic statement value; and `Jrewrite` changes the proof bytes delivered to
a transcript-observed message occurrence.
For each `Jx`, fix `Bx` as the exact every-and-only least Interface algorithm
dependency closure, `Ax` as matching dependency-authentication capabilities,
`Vx` as the resulting retained views, and `Lx` as exact identity-matched
`ExactInterfaceLawCheckerCapabilities`.

**Initial subject and authority state.** `cap(PF)` exists. Each `Jx`, `Bx`,
`Ax`, and `Lx` is a raw operation input; no authenticated Interface handle,
`Vx`, or admitted Interface capability exists.

**Operation and exact result.** For each `Jx`,
`AuthenticateProtocolInterface(Jx, Bx, Ax)` succeeds physically and
recomputes its dependent candidate identity. Then
`AdmitProtocolInterface(authenticated Jx, exact PF view, Vx, Lx)` returns,
respectively:

```text
Negative(SemanticDomainRestriction)
Negative(SemanticDefaultInjection)
Negative(TranscriptVisibleRewrite)
```

`Jrestrict` belongs in an external policy or a checked adapter into an admitted
Interface domain. `Jdefault` needs an explicit adapter or wrapper that owns the
new accepted external language. `Jrewrite` changes a protected Protocol
observation and therefore requires a wrapper or new Core/Protocol identity.

**Identity effects.** Each authenticated candidate may have a recomputed
`ProtocolInterfaceId`, but no rejected candidate becomes an admitted
Interface. `pF` remains unchanged. A wrapper that changes meaning receives its
own Protocol ID.

**Capability and replay effects.** Candidate IDs cannot be passed as admitted
Interface capabilities. Replay reauthenticates the exact `Bx` with local
`Ax`, obtains fresh `Vx`, reacquires `Lx`, and reruns the same negative
admission; a dependency or checker cannot be inferred from an ID. Policy or
adapter authority is separately typed and cannot be inferred from the
candidate.

**Preserved nonclaims.** Rejection does not say the proposed external behavior
is undesirable or impossible; it says it is not a meaning-preserving
Interface for `pF`.

**Decisive falsifier.** Any candidate is admitted while changing the Protocol
domain, a semantic default, transcript framing, canonical message bytes,
challenge derivation, or accepted language.

## 5. Relations

### L1 — relation ingress before bytes and later artifact comparison

**Status:** Pass.

**Declared immutable inputs.** Admit exact artifact profile `phi`, adapter
contract `A`, and relation interface `RI`, then fix binding candidate `RB`
without artifact bytes. `RI` declares no committed-object occurrence and
`RB.committed_object_grounding = {}`. Every public- or witness-occurrence map
entry contains its exact allowed Protocol target—an exact
`ProtocolPublicAssignmentOccurrence(ProtocolPublicStatementOccurrenceRef)` for
each public entry or the exact allowed private-Prover occurrence for each
witness entry—plus an identity-bearing
`RelationToProtocolValueBridge` whose two algorithm ABIs name the exact
relation and Protocol domains and satisfy both round trips. Fix `DB1` as the
every-and-only least dependency closure of those bridge algorithms, keyed by
`TypedRelationBindingAlgorithmDependencyRef` retaining exact kind, regime,
content ID, ABI, and direct edges; fix `AB1` as
the exact matching dependency-authentication capabilities, `VB1` as the
retained attenuated views, and `LB1` as the exact identity-matched binding-law
checker capabilities. The exact required admitted-adapter-view input is empty,
so binding formation and admission consume neither `cap(A)` nor an artifact
observation; `A` is used only by the later artifact interpretation. Later supply matching
exact raw bytes `bm` and well-formed conflicting exact raw bytes `bc`.
The admitted `phi` retains the every-and-only byte-language closure rooted at
its `ExactByteLanguageContractRef`, keyed by full
`TypedRelationArtifactProfileDependencyRef`; admitted `A` retains the
every-and-only deterministic-interpreter closure rooted at its
`ExactDeterministicInterpreterContractRef`, keyed by full
`TypedRelationAdapterDependencyRef`. Both typed keys retain kind, contract
regime, content ID, exact ABI, and direct dependency IDs.
The conflict changes only one interpreted public-port cardinality; all other
emitted facts agree. Fix artifact comparison question `Qartifact` to the
public-port fields and correspondence question
`Qcorr = {base_clauses = {PublicPorts, WitnessPorts,
ResultBindingReferenceShape}, artifact_question = Some(Qartifact)}`.
Fix `Einterp` as the exact identity-matched
`ExactRelationAdapterInterpreterExecutionCapabilities` for admitted adapter
`A` and profile `phi`.

**Initial subject and authority state.** `cap(PF)`, `cap(I)`, `cap(phi)`,
`cap(A)`, and `cap(RI)` exist. Raw `RB`, `DB1`, `AB1`, and `LB1` and exact
`Einterp` are available, but `cap(RB)` and `VB1` do not yet exist. `cap(A)` and
`Einterp` authorize only the separate interpretation and observation-admission
path. There is no artifact observation or artifact-derived authority.

**Operation and exact result.** First,
`AuthenticateRelationBinding(RB, DB1, AB1)` and
`AdmitRelationBinding(authenticated RB, exact PF binding view, I, RI, VB1, {},
LB1)` are affirmative and mint `cap(RB)` without reading artifact bytes or
`A`. Then `InterpretRelationArtifact(bm, phi, A, Einterp)` and
`InterpretRelationArtifact(bc, phi, A, Einterp)` return `Completed` candidates `CmRaw`
and `CcRaw`; interpretation reads no expected relation and makes no agreement
claim. For each pair `(bytes, candidate)`, run
`AuthenticateRelationArtifactObservation(candidate, bytes, phi identity view,
A identity view)` and then
`AdmitRelationArtifactObservation(authenticated candidate, bytes, phi, A,
Einterp)`. Those calls mint admitted observations `Om` and `Oc`; a candidate,
claimed observation ID, or serialized result cannot enter comparison. Then:

```text
RelationArtifactAgreesWithInterface(Om, RI, Qartifact, rhoCorr)
  -> Affirmative(CheckedArtifactInterfaceComparison Am)
RelationArtifactAgreesWithInterface(Oc, RI, Qartifact, rhoCorr)
  -> Negative(CheckedArtifactInterfaceComparison Ac,
              public_port_cardinality,
              retained_agreements)
```

With all other bridge fields fixed,
`RelationCorrespondsAtInterface(..., Qcorr, Am, None, rhoCorr)` is affirmative
and mints `CheckedRelationCorrespondenceJudgment Jm`. The same exact
correspondence request with checked negative comparison `Ac` is negative,
mints `CheckedRelationCorrespondenceJudgment Jc`, makes the artifact field
outcome negative, and retains the unaffected base-clause facts. Both `Am` and
`Ac` retain the identical nested `Qartifact`; a
result over a strict subset or different field question is not widenable to
`Qcorr.artifact_question`. Neither path makes `PF`, `I`, or `RI` malformed.
Passing only `Oc` without the checked comparison would instead be
`CannotAnswer`.

**Identity effects.** Protocol, Interface, relation definition, and relation
interface identities are unchanged by later bytes. `bm` and `bc` produce
distinct `RelationArtifactByteId`s and therefore distinct observation IDs.

**Capability and replay effects.** Serialized observation material carries no
profile, adapter, observation, `CheckedArtifactInterfaceComparison`, or
`CheckedRelationCorrespondenceJudgment` capability.
Replay re-authenticates and re-admits `phi` and `A`, re-supplies the exact raw
bytes so their `RelationArtifactByteId` is recomputed, reauthenticates `RB`
with exact `DB1` and locally reacquired `AB1`, re-admits it with fresh `VB1`
and `LB1` plus the empty adapter-view set, reruns interpretation, then runs the
exact observation authentication and admission calls with newly reacquired
`Einterp` before rerunning the exact comparison and correspondence questions.

**Preserved nonclaims.** Agreement proves only equality of interpreted fields.
It does not prove the external definition's meaning, satisfiability, instance
truth, witness validity, or correspondence beyond checked fields.

**Decisive falsifier.** Relation-interface admission requires artifact bytes;
interpretation reads an expected relation; matching bytes establish relation
truth; a comparison over a subset or different question is widened to
`Qcorr.artifact_question`; or a checked conflict cannot produce a field-
factored negative correspondence without invalidating Protocol admission.
Binding dependency or checker authority inferred from an ID or ambient
registry is an additional falsifier.

### L2 — one negative correspondence field

**Status:** Pass.

**Declared immutable inputs.** `PF`, `I`, and `RI` are individually well formed
and admitted; `RBwrong` is a well-formed binding candidate. For this scenario
only, `PF` has one public `Statement` input port of multiplicity
`FixedCount(2)`, with exact occurrences `s0` and `s1`, each an in-`PF`
`ProtocolPublicStatementOccurrenceRef`, and `I`'s
`CanonicalPublicAssignmentDomain` contains both exactly once. `RI` declares
exactly one public occurrence `rpub0` and exactly one witness occurrence, no
committed-object occurrence, and an exact finite tri-state result domain
`Dtri = {satisfied, unsatisfied, indeterminate}` with nonempty
`accepted_values = {satisfied}`. `PF` contains an exact invoked Boolean check
`k`, and `RBwrong` owns total public- and witness-occurrence maps. Its sole
public entry is
`RelationPublicPortBinding {target =
ProtocolPublicAssignmentOccurrence(s0), value_bridge = Bpub}`. Its witness entry
is `RelationWitnessPortBinding {target = exact private Prover input occurrence
or named prover-obligation output, value_bridge = Bwit}`. Each `Bpub` or `Bwit`
names its exact relation source domain and Protocol target domain, contains
total canonical `to_protocol` and `to_relation` algorithms with those exact
ABIs, and satisfies both two-sided round trips. Literal domain identity is
used only when the regime-qualified contract is exactly shared; byte equality
or equal cardinality is insufficient.
`RBwrong.committed_object_grounding = {}`. Fix `DB2` as the every-and-only
least closure of all those bridge algorithms, keyed by exact
`TypedRelationBindingAlgorithmDependencyRef`; fix `AB2` as the exact matching
dependency-authentication capabilities, `VB2` as the retained views, and
`LB2` as the exact binding-law checker capabilities; required adapter views
are empty.
Its kind-correct `result_binding = CheckTrue(k)` names that exact Boolean check,
so binding admission succeeds. The admitted binding is total over all relation
occurrences and target-unique, but it does not claim target-surjectivity over
the Interface's two Protocol statement occurrences: `s1` is intentionally
unmapped. Fix
`Qbase = {base_clauses = {PublicPorts, WitnessPorts,
ResultBindingReferenceShape}, artifact_question = None}`.

**Initial subject and authority state.** All subject capabilities except
`cap(RBwrong)` are live in one process. Raw `RBwrong`, `DB2`, `AB2`, and `LB2`
are available; `VB2` and binding authority do not yet exist. No witness value
or satisfaction result is supplied.

**Operation and exact result.**
`AuthenticateRelationBinding(RBwrong, DB2, AB2)` and
`AdmitRelationBinding(authenticated RBwrong, exact PF binding view, I, RI,
VB2, {}, LB2)` are affirmative: all bridge, occurrence, and reference-shape
laws pass. The main call then returns:

```text
RelationCorrespondsAtInterface(..., RBwrong, Qbase, None, None, rhoCorr)
  -> Negative(
       public_port_cardinality_mismatch(
         relation_occurrences = {rpub0},
         Protocol_statement_occurrences = {s0, s1},
         unmatched_Protocol_occurrences = {s1}),
       retained_facts = {
         rpub0-to-s0 bridge and position agreement,
         witness-role and bridge agreements,
         result-binding-reference-shape agreement
       })
```

This completed negative outcome mints
`CheckedRelationCorrespondenceJudgment Cwrong`. It records the exact identified
subjects and `Qbase` as judgment metadata; it does not turn that metadata into
an agreement on an unrequested correspondence clause.

Control calls establish outcome separation. Removing `cap(RBwrong)` while
retaining its bytes and ID yields `Refused(missing binding authority)`.
Changing the question to
`Qground = {base_clauses = Qbase.base_clauses +
{CommittedObjectGrounding}, artifact_question = None}` while omitting any exact
checked grounding result yields
`CannotAnswer(missing CheckedCommittedObjectGrounding)`.
An unknown correspondence clause yields `Unsupported`; malformed binding
transport fails before the semantic check; an operational checker crash yields
`CheckerFailure` and no field conclusion.

**Identity effects.** The negative judgment changes no subject ID. It is a
result about exact identified inputs, not a revised Interface or Protocol.

**Capability and replay effects.** The negative outcome mints a
`CheckedRelationCorrespondenceJudgment` scoped to the exact checker, regime,
inputs, question, and retained facts. It cannot be widened to another binding
or reconstructed from a report string. Replay reauthenticates
the every-and-only bridge closure with fresh `AB2`, retains new `VB2`, and
re-admits with local `LB2`; an ID or report grants none of this authority.

**Preserved nonclaims.** The negative result refutes only the requested
`PublicPorts` cardinality/position alignment. It retains witness agreement and
the well-formed `CheckTrue(k)` reference. `ResultBindingReferenceShape` does
not compare `Dtri`, `accepted_values`, or any Protocol result semantics and
cannot establish that relation acceptance holds if and only if Protocol
acceptance. The result does not refute the relation definition, relation
instance, or existence of some other valid Interface or binding.

**Decisive falsifier.** The one public-port mismatch discards unaffected agreements, becomes
Protocol malformedness, or is conflated with missing input, missing authority,
unsupported semantics, or checker failure; or a bridge domain/round trip or
binding dependency/capability is inferred rather than checked exactly.

### L3 — grounding an opaque committed object

**Status:** Pass.

**Declared immutable inputs.** `C` declares object `o` under exact
`ProtocolObjectContractRef q`. The ABI of `q` fixes Protocol object domain
`Dprotocol`, exact constructor-input domains `[Dstmt]`, a total deterministic
construction relation `Construct_q : Dstmt -> Dprotocol`, and canonical
equality and encoding operations over `Dprotocol`. It exposes no ambient read.
The exact declaration of `o` is:

```text
contract = q
constructor_inputs = [PortValue(PortOccurrenceRef(statement, 0))]
owner_role = Prover
visibility = Public
protected_observations = {Wire}
```

The statement occurrence has domain `Dstmt`. The constructed object is named
at input ordinal zero of Prover-to-Verifier proof-channel message `mo` and used
nowhere in a transcript atom, check, artifact, or claim, so `{Wire}` is the
recomputed complete observation envelope. `I` binds `mo` through an exact
`GuardedProofTraceBinding` to external proof position `xmo`; its encoder and
decoder round-trip the guarded proof-message semantic trace containing `mo`
and object input ordinal zero at that position. It makes no Relations-owned
material-domain claim.
`RI.public_ports = []` and `RI.witness_ports = []`, isolating the object-
grounding question from value bridges. It declares an `ExactlyOne`
committed-object role `r` with

```text
r.semantic_object_domain = Dobj
r.commitment_value_domain = Dcommit
r.material_value_domain = Dmaterial
```

and `r0 = RelationCommittedObjectRef(r, 0)`. Fix three closed, deterministic,
total algorithm specs:

```text
Ssemantic : ProtocolObjectToRelationSemanticObject
            (q, Dprotocol) -> Dobj
Scommit   : RelationObjectToCommitmentValue
            Dobj -> Dcommit
Smaterial : RelationObjectToCanonicalMaterial
            Dobj -> Dmaterial
```

Their typed syntax or content-addressed contract preimages, exact ABIs, and
direct dependency closures are immutable inputs. Fix `DG` as the exact
`ExactRelationBindingAlgorithmDependencyBundle` containing every and only
content-addressed preimage in their least closure, keyed by
`TypedRelationBindingAlgorithmDependencyRef` retaining kind, regime, content
ID, ABI, and direct edges; closed finite terms have no entry. Fix `AdepG` as
the exact matching dependency-authentication
capabilities, `VG` as the resulting retained dependency views, and `LG` as the
exact identity-matched binding-law checker capabilities. Fix `EG` as the exact
`ExactGroundingAlgorithmExecutionCapabilities` for these three identity-
matched algorithm views.

Fix exact admitted artifact profile `phiG`, exact admitted adapter `AG`, exact
raw bytes `bG`, and admitted observation `OG`. `AG`'s identity-bearing
`ExactDeterministicInterpreterContractRef` deterministically emits typed fact
`fG` from `bG`; exact selector `selectorG` selects only `fG`. `OG` was formed by
the exact interpretation, observation-authentication, and observation-
admission lifecycle and retains the identical `phiG`, `AG`,
`RelationArtifactByteId(bG)`, and `fG`. Thus `cap(AG)` is the exact adapter
authority named by the binding and `cap(OG)` is exact relation-material
authority, not raw bytes or a parsed assertion.

`RB.public_port_map`
and `RB.witness_port_map` are both empty, and `RB` contains the following
identity-bearing grounding entry, not a free adapter assertion:

```text
RB.committed_object_grounding[r0] = {
  protocol_object = CoreRef<object>(c, o),
  semantic_object_derivation = Ssemantic,
  commitment_value_derivation = Scommit,
  material_encoding = Smaterial,
  interface_position = ProofMessageObject(xmo, EventInputOrdinal(0)),
  artifact_dependency =
    FromArtifactFact(RelationAdapterRef(AG), selectorG)
}
```

Its result binding is the fixed kind-correct fixture value. Exact
`CorrespondenceRegime rhoG` and exact
`ConditionalArtifactObservationMap MG = {r0 -> OG}` are supplied.

**Initial subject and authority state.** Protocol admission has authenticated
only `o`'s Protocol-facing declaration; it has not interpreted relation
meaning. Binding authentication consumes the exact preimages and direct
closures in `DG`; binding admission checks their ABIs, occurrence totality,
the exact object reference, and the proof-position/input-ordinal chain. Live
capabilities exist for the admitted Protocol object-declaration/binding view,
`I`, `RI`, `phiG`, `AG`, `OG`, `AdepG`, `LG`, `EG`, and `rhoG`. Raw `RB` and
`DG` are present, but `cap(RB)` and `VG` do not yet exist. Bytes `bG`, a
profile or adapter ID, and the selected fact alone grant no authority.

**Operation and exact result.** First,
`AuthenticateRelationBinding(RB, DG, AdepG)` and
`AdmitRelationBinding(authenticated RB, exact Protocol binding view, I, RI,
VG, {AG}, LG)` are affirmative. The exact grounding call is:

```text
GroundCommittedObjects(
  admitted Protocol object-declaration view,
  I,
  RI,
  RB,
  VG,
  EG,
  MG,
  rhoG)
  -> Affirmative(CheckedCommittedObjectGrounding G0)
```

`G0` binds exact object reference `o` to exact relation occurrence `r0`, the
three declared derivations and domains, and exact Interface position
`ProofMessageObject(xmo, EventInputOrdinal(0))`, plus the exact assigned
artifact derivation through `AG`, `selectorG`, and `OG`. Replacing `MG` with
the empty map is `CannotAnswer(missing required artifact observation)`;
supplying an observation with a different adapter, profile, raw-byte identity,
or selected fact is `CannotAnswer(mismatched required artifact observation)`.
`RelationCorrespondsAtInterface` may then consume this exact grounding rather
than a raw adapter assertion.

**Identity effects.** Grounding changes none of `CoreId`, `ProtocolId`,
`ProtocolInterfaceId`, `RelationInterfaceId`, or `RelationBindingId`.

**Capability and replay effects.** `G0` is a
`CheckedCommittedObjectGrounding` capability bound to the exact object
declaration, Interface, relation role, binding, all three
algorithm specs, `DG`, `VG`, exact admitted `AG` and `OG`, `MG`, `EG`, and
`rhoG`. Replay reauthenticates every algorithm preimage and direct
dependency with freshly acquired `AdepG`, retains new `VG`, re-admits `RB`
with newly reauthenticated/re-admitted `AG` in its exact admitted-adapter-view
set and local `LG`, re-supplies `bG`, reruns interpretation plus observation
authentication/admission to mint a fresh local `OG`, reacquires exact
identity-matched `EG`, reconstructs `MG`, and reruns the exact call.
Substituting only a digest, parsed fact, or instance-wiring map is refused.

**Preserved nonclaims.** Grounding checks the three declared contract
equations and exact position chain; it does not prove that those algorithms
or `AG`'s external format interpretation are mathematically faithful. Exact
artifact fact agreement proves neither opening knowledge, commitment
binding, witness possession, witness satisfaction, relation truth, nor a
cryptographic property. It also does not elevate `q`'s Protocol-local object
construction into an interpretation of the relation's mathematical meaning.
The singleton fixture establishes neither inverse coverage nor injectivity:
Protocol objects outside the grounding map need not be covered, and distinct
relation occurrences may name one Protocol object only under their own
independently checked domains and derivations.

**Decisive falsifier.** Raw bytes, a material digest, or adapter availability
grounds `o` without the exact bindings; the invocation chooses a codec,
adapter, artifact fact, or Interface position; binding admission succeeds
without the exact admitted `AG` view; grounding succeeds without exact `MG` or
with a mismatched observation; a grounding execution capability is missing or
mismatched; grounding mutates Protocol identity; or an affirmative grounding
is accepted as `RelationSatisfies`.

## 6. Plan and realization seam

### R1 — multiple Plans and supplier strategies

**Status:** Pass for the Stage 3 partition law under one explicitly
hypothetical observer. This is not a v0 OIR design or a durable Stage 4B field
classification.

**Declared immutable inputs.** `PlanA` and `PlanB` depend on `pF` and cover the
same prover obligations. `PlanA` names these exact field references:

```text
a.input.witness
a.node.direct
a.hole.commitment
a.dependency.direct_ops
a.dependency.hole_ops
a.dependency.msm_supplier
a.requirement.msm
a.route.proof_message
```

`PlanB` names the corresponding `b.input.witness`, two factored nodes
`b.node.prepare` and `b.node.finish`, `b.hole.commitment`,
`b.dependency.prepare_ops`, `b.dependency.finish_ops`,
`b.dependency.hole_ops`, `b.dependency.msm_supplier`,
`b.requirement.msm`, and
`b.route.proof_message`. `SupplierX` and `SupplierY` are two live strategies
that could satisfy the same `*.requirement.msm`; they are not Plan fields or
Protocol inputs.

In both Plans, `C.witness` is an exactly-one, Prover-owned,
`PrivateToRole`, `Witness` input port. `*.input.witness` has its exact value
domain and source
`ProtocolPrivatePortOccurrence(PortOccurrenceRef(C.witness, 0))`; each Plan
names that occurrence exactly once and reuses it only through that one
`PlanInputRef`, never through a second alias. The descriptor contains no
witness value. Across every node, hole, and transitive operand edge,
`ProtocolAvailableValueRef` categorically excludes that private witness
origin and every raw `PrivateRandomnessValue`; only
`PrivateProtocolPlanInputRef(*.input.witness)` may name this witness, and this
fixture has no raw private-randomness operand on any node, hole, basis map, or
transitive edge. Its only private-randomness ingress is the typed
`UsesProtocolRandomness` effect channel declared below.
Each `*.requirement.msm` targets the exact `*.hole.commitment`, names the same
admitted supplier contract, and has `ExactlyOne` multiplicity.
Each `*.dependency.*_ops` entry has kind `ProverConstructionContract` and an
exact ABI backing only its correspondingly named node or hole, including the
declared ordered private-effect inputs. The distinct
`*.dependency.msm_supplier` has kind `SupplierContract` and backs exactly that
requirement. Each Plan's least closed `private_dependencies` graph contains
every one of these kind-correct preimages and their exact direct closure;
neither dependency
kind is reinterpreted as the other. A runtime
private value for that exact Plan input and the supplier handles are
occurrence-local inputs and are deliberately absent from both immutable Plan
preimages. For each `PlanX`, fix `BPx` as the exact
`ExactPlanDependencyPreimageBundle`, `APx` as its exact kind/regime/content/
ABI-matched `ExactPlanDependencyAuthenticationCapabilities`, `VPx` as the
resulting retained dependency views, and `LPx` as its exact identity-matched
`ExactPlanLawCheckerCapabilities`. The bundle and declaration map both equal
the every-and-only least `private_dependencies` closure.
Fix exact `PlanRealizesRegime rhoRealizes` for both structural
realization questions.

Let `oProof` be the sole routed prover obligation and specialize this fixture
with two distinct owner-matched private-randomness occurrences `r0` and `r1`
of the same admitted domain. Its identity-bearing Core basis is
`oProof.private_randomness = [r0, r1]`, the exact pre-action attempt order.
In `PlanA`, `a.node.direct` has
`UsesProtocolRandomness([PlanPrivateRandomnessRef(r0),
PlanPrivateRandomnessRef(r1)])` and feeds `a.hole.commitment`, which is the
route producer. In `PlanB`, `b.node.prepare` has
`UsesProtocolRandomness([PlanPrivateRandomnessRef(r0)])` and feeds
`b.node.finish`; `b.node.finish` has
`UsesProtocolRandomness([PlanPrivateRandomnessRef(r1)])` and feeds
`b.hole.commitment`, the route producer. Their canonical node ordinals order
`b.node.prepare` before `b.node.finish`. Each exact node contract's private-
effect ABI matches its own sequence in length, order, domains, and purposes.
In each Plan, each source appears in exactly one effect-input occurrence,
every randomized node runs after its referenced exact successful sampling
step and before `oProof`'s outputs bind, and reuse can flow only through
ordinary node outputs.

Thus every named node and hole has the exact nonempty
`DownstreamObligationRoutes = {oProof}`. Under the canonical node-ordinal then
effect-input-ordinal scan of the route producer's transitive subgraph, both
Plans satisfy
`RouteRandomnessIngresses(oProof) = [r0, r1] =
oProof.private_randomness`. This is exact ordered, owner-matched coverage, not
an inference from equal domains or supplier behavior. Each
`*.route.proof_message.basis_input_map` is total over every and only
`ProverObligationInputOrdinal` of `oProof`. A Core basis operand equal to
`PortValue(C.witness, 0)` maps to the unique
`PrivateProtocolPlanInputRef(*.input.witness)` whose source is exactly
`ProtocolPrivatePortOccurrence(C.witness, 0)`. Every other admissible Core
basis operand maps to the same-kind exact `ProtocolAvailableValueRef` or
`ProtocolAvailableObjectRef`; neither an `ExternalSecret` nor a raw
`PrivateRandomnessValue` can satisfy a Core basis ordinal. Each binding
preserves exact occurrence and domain and is a
transitive dependency of the route producer. Each route's `output_map` is the
exact bijection from every `oProof` output ordinal to the route producer's
same-domain output ordinals. For every Protocol value/object operand and this
downstream route, direct Core path reasoning proves
`EventAttempted(source_event(oProof))` implies
`AvailableAt(Prover, operand, PreAttempt(source_event(oProof)))`. The exact
singleton-owner/effect-occurrence and sample-to-binding timing conditions are
established directly rather than delegated to a supplier.

Fix four `PlanA` counterexample candidates with every unmentioned field held
exact. `PlanMissing` changes the direct node's effect to `[r0]` and uses a
matching one-input contract ABI. `PlanReordered` uses `[r1, r0]` and its exact
matching two-input ABI. `PlanExtra` uses `[r0, r1, r0]` with a matching
three-input ABI, duplicating one direct ingress. `PlanBypass` removes `r0` from
the effect channel and instead attempts to place raw
`PrivateRandomnessValue(r0)` in an ordinary node operand by falsely spelling
it as `ProtocolAvailableValueRef`; its remaining declared effect is `[r1]`.
Each candidate has its own exact identity-bearing dependency preimages,
same-key authentication capabilities, retained views, and identity-matched
Plan law checkers. No variant relies on changing an ABI behind a fixed
dependency identity.

For this falsification only, supply immutable hypothetical observer `Omega`.
`Omega` observes explicit prover-OIR inputs, value/event dependency structure,
hole boundaries, operation contracts, and obligation routes. It holds those
fixed while ignoring implementation algorithm, execution schedule, buffering,
resource allocation, and live supplier choice. `Omega` is a scenario fixture,
not a proposed OIR grammar, identity, checker capability, or Stage 4B result.

**Initial subject and authority state.** `cap(PF)` exists. The two Plans begin
as raw candidates with their exact `BPx`, `APx`, and `LPx` operation inputs but
without retained `VPx`, authenticated handles, or Plan admission authority. No
production OIR, projection result, field-classification capability, private-
input value, supplier authority, or supplier-correctness judgment exists.
The four counterexamples likewise begin as raw candidates with no subject or
result authority.

**Operation and exact result.** For each `PlanX`, first run
`AuthenticateProverPlan(PlanX, BPx, APx)`, then
`AdmitProverPlan(authenticated PlanX, exact PF plan-typing view, VPx, LPx)`.
Both boundaries are affirmative. A missing, extra, aliased, or
kind/regime/content/ABI-mismatched dependency, retained view, or capability is
refused or fails its owning boundary rather than being resolved ambiently.
`PlanRealizes(PF, PlanA, rhoRealizes)` and
`PlanRealizes(PF, PlanB, rhoRealizes)` are then separately affirmative and mint
`CheckedPlanRealizes KA` and `CheckedPlanRealizes KB`: each has one total,
typed route per exact prover obligation and neither changes verifier-visible
events, wire values, transcripts, challenges, checks, failures, terminals, or
accepted language. Each result retains its exact `ProverPlanId` and
`rhoRealizes`.

`PlanMissing` and `PlanReordered` are locally well typed and each authenticates
and admits under its own exact ABI and authority inputs. Their separate
`PlanRealizes` calls return successful negatives retaining, respectively,
`RouteRandomnessIngresses(oProof) = [r0] != [r0, r1]` and
`RouteRandomnessIngresses(oProof) = [r1, r0] != [r0, r1]`. Total coverage and
Core basis order are relation-owned, so neither local admission is widened
into realization. `PlanExtra` authenticates but admission is negative because
one Core private source has two direct effect ingresses. `PlanBypass`
authenticates as a raw candidate but admission is negative because a raw
`PrivateRandomnessValue` cannot inhabit `ProtocolAvailableValueRef` or any
ordinary/transitive Plan operand. Neither inadmissible candidate can be passed
to `PlanRealizes`.

Apply the target model's substitution rule relative to `Omega` to every named
field:

| Fixture fields | `Omega` observation under substitution | Exact placement in this probe |
|---|---|---|
| `*.input.witness` | Changes explicit OIR-local input contract | `ProjectionRelevant` |
| `*.node.*` | Changes canonical value/event dependency structure | `ProjectionRelevant` |
| `*.hole.commitment` | Changes explicit OIR hole/input boundary | `ProjectionRelevant` |
| `*.dependency.*_ops` | Changes an exact operation contract read by the OIR graph | `ProjectionRelevant` |
| `*.dependency.msm_supplier` | Backs only the typed external-supply requirement that `Omega` leaves below the fixed obligation interface | `ExternalSupplyRequirement`, resolved to realization placement in this probe |
| `*.route.proof_message` | Changes the OIR route to a Protocol obligation | `ProjectionRelevant` |
| `*.requirement.msm` | Declares external supply, but `Omega` exposes no supplier choice and fixes only the obligation interface | `ExternalSupplyRequirement`, resolved to realization placement in this probe |
| `SupplierX` / `SupplierY` | No observed OIR field changes | Outside Plan classification; realization-local live inputs |

The Plan-field sets are disjoint and cover every named Plan field; the two
supplier strategies are deliberately outside that partition. Because
projection reads a Plan field, a hypothetical OIR identity under `Omega` would
commit to the full exact Plan ID. Before an actual Stage 4B observer and
checker exist, the corresponding v0 classification request remains
`CannotAnswer(missing exact OIR semantics)`, never an ambient guess.

**Identity effects.** `pF` is stable;
`ProverPlanId(PlanA) != ProverPlanId(PlanB)`. Supplier strategy substitution
does not alter either ID because live supplier handles are not Plan fields.
Every counterexample field or contract substitution computes a distinct Plan
identity while leaving `pF` fixed. The probe assigns no durable OIR or
classification identity.

**Capability and replay effects.** Each `CheckedPlanRealizes` capability cites
the exact admitted Plan, Protocol, and `rhoRealizes`; `KA` cannot be widened to
`PlanB` or `KB` to `PlanA`. Supplier handles remain realization-local. Neither
a Plan ID nor `CheckedPlanRealizes` authorizes a live supplier. Replaying the partition
probe requires the same `Omega`; substituting a production OIR observer is a
new Stage 4B check. Re-authenticating either Plan needs its secret-free
descriptor, exact `BPx`, and locally reacquired matching `APx`; re-admission
uses new retained `VPx` and local `LPx`, then reruns
`PlanRealizes(PF, PlanX, rhoRealizes)`. The occurrence-local private-input
value and supplier handles are
realization-local inputs, but they are not yet a complete execution boundary:
Stage 4B must additionally construct and prove the exact agreement of
`CoreInvocationInputs`, `ProverTrace`, and `RandomnessReplay` before
invoking `ExecuteProtocol` with the exact admitted Protocol capability and
identity-matched `ExactProtocolExecutionCapabilities`, never a Protocol ID or
raw Protocol. Neither a Plan nor `CheckedPlanRealizes`
supplies that bridge.
Changing those live values or handles does not change the Plan ID or
retroactively alter a structural `CheckedPlanRealizes` result.
Negative realization checks mint no affirmative result authority, and the two
admission failures mint no `AdmittedPlan`; replay of any variant starts from
its own exact preimages and local checker capabilities.

**Preserved nonclaims.** `PlanRealizes` does not prove provider correctness,
witness validity, termination, honest-prover completeness, successful proof
production, cost, performance, or that runtime samples followed the declared
probability law.

**Decisive falsifier.** Plan or supplier substitution changes verifier meaning;
a named fixture field is unclassified or appears in both placement sets; a
Plan-sensitive result omits the Plan ID; a dependency or checker is inferred
from an ID or ambient registry; a supplier is ambiently resolved; or the
hypothetical `Omega` result is presented as v0 OIR authority; or missing,
extra, reordered, owner-mismatched, or raw-value-bypassing private-randomness
ingress yields affirmative `CheckedPlanRealizes` or admission authority at the
wrong boundary.

## 7. Fiat--Shamir construction and property seams

### F1 — admitted FS target without theorem basis

**Status:** Pass.

**Declared immutable inputs.** Supply admitted fresh Protocol `PF` and an exact
`TranscriptConstruction T` candidate scoped to `c` and interpreted under
`rhoP`; in this fixture the Core's sole public challenge source is
`IndependentFresh`. Supply T's codec/framing/sampler dependencies,
initialization and framing,
total event-action table, recomputable challenge-prefix table, abort map, and
application domain. This fixture declares no public Input `Context` port
occurrence, so `session_context_map` is the exact empty total map and
`ExactCompositionContext = Standalone` binds no composition history or
composition-owned entry. Every challenge-prefix entry is the exact canonical
sequence of `EventActionOccurrenceRef`s for prior potentially action-occurring
events whose mapped action is non-no-op `Absorb` or `DeriveChallenge`, in total
Core schedule order, with their derived action-occurrence predicates retained.
It is the exact action-wise image of the Core template after excluding
`NoTranscriptAction`; at runtime it selects the exact action-occurring
subsequence. Every absorbed atom is an
`ExactEventInputOccurrenceRef` to an in-range input ordinal of that same event,
appears in canonical input order, and carries that input's exact semantic type
and codec; there is no event-output atom source. No
source-to-target occurrence, challenge, or prefix map is supplied; no
`FSCompile` semantic model or theorem/rule is supplied after construction.
The initialization contract, session-context initialization, framing, every
`InitializationAction`, and every `TypedTranscriptAtom.codec` have total,
infallible Protocol-facing ABIs over their admitted typed domains. The sole
fallible transcript transition is this challenge's `SqueezeAndSampleRule`; its
only non-success is the exact occurrence-indexed `SamplingFailed` continuation
named by `T.abort_map` and the Core challenge bundle. Malformed external bytes
remain a pre-Protocol Interface or wrapper outcome and cannot become a
transcript runtime failure.
Fix `BT` as the every-and-only least dependency closure of all
content-addressed initialization, framing, atom-codec, and squeeze rules in
`T`, keyed by `TypedTranscriptAlgorithmDependencyRef` retaining exact kind,
regime, content ID, ABI, and direct edges; closed finite terms have no entry.
Fix `AT` as the exact matching
kind/regime/content/ABI/edge dependency-authentication capabilities, `VT` as
the resulting retained attenuated views, and `LT` as the exact identity-
matched `ExactTranscriptLawCheckerCapabilities`. `T` is authenticated and
admitted exactly by
`AuthenticateTranscriptConstruction(T, BT, AT)` followed by
`AdmitTranscriptConstruction(authenticated T, core_view(PF),
NoCompositionContext, VT, LT)`. A composed construction would instead require the
transaction-scoped formation authority during target formation or the later
affirmative `CheckedCoreComposition`; a spec ID or serialized child list would not
suffice. Fix the target authentication input
`Bfs = {core_dependencies = every and only member of the target Core's least
dependency closure, transcript_construction = exact T candidate plus BT}` and
its exact matching dependency-authentication capability record
`AdepFS = {core = exact same-key map as Bfs.core_dependencies,
transcript = exact freshly reacquired AT}`.
Fix resulting retained target Protocol dependency views `Vtarget`, exact
target admission checker bundle
`Ltarget = {core = LcoreTarget, transcript = LTtarget}`, and exact
`FSConstructionRegime rhoFS`. Target admission uses
`NoCompositionContext` because this construction is `Standalone`.

**Initial subject and authority state.** `cap(PF)` exists. The raw `T`, `BT`,
`AT`, and `LT` are available as exact operation inputs, but `cap(T)`, the FS
target, and construction-result authority do not yet exist.

**Operation and exact result.** The exact authentication and admission calls
above mint `cap(T)`. A missing, extra, kind/regime/content/ABI/edge-mismatched
dependency or mismatched authentication/law-checker capability fails its
owning boundary. `ConstructFS(PF, T)` then deterministically emits an
FS target candidate plus one `FSConstructionMaps` value. The map value names
the exact source and target Protocol IDs, stores their one literal
`shared_core_id` as the `CoreId` of both admitted subjects, and records
`interpretation_change = FreshToFiatShamir(T.id)`. Its event and challenge
maps are total bijections over their respective Core domains; every entry uses
the exact source/target `ProtocolScopedRef` and preserves the inner `CoreRef`,
so equal inner references do not alias the Fresh and FS interpretations. Each
`FSTargetPrefixDescriptor` names the mapped target challenge, its exact
potential Core `EventActionOccurrenceRef` prefix, the exact non-no-op
transcript-action image of that prefix, and its exact action-occurring runtime
projection. The target canonical PIR stores the exact
`TranscriptConstructionId`.
`AuthenticateCanonicalPir_rhoP(target, Bfs, AdepFS)` authenticates the separate
construction preimage and its complete dependency closure as well as the
target Core closure. Independent target admission is the exact public call
`AdmitProtocol(authenticated target, Vtarget, NoCompositionContext, Ltarget)`.
It internally mints a fresh scoped Core witness, uses the retained
authenticated construction and its `VTtarget` algorithm views plus
`LTtarget` to re-admit `T` against that witness, admits the enclosing Protocol
as `Pfs`, and discards the witness. It refuses a missing transcript checker,
an extra checker, or one scoped to another construction. Only then run:

```text
FinalizeFSConstruction(PF, Pfs, admitted T, FSConstructionMaps, rhoFS)
  -> Affirmative(CheckedFSConstruction Kfs)
```

Finalization directly recomputes every identity, interpretation, event,
challenge, and prefix equation; map possession alone mints no result.
For a Fresh challenge, its `DeriveChallenge` transcript action is an
action-occurring resolution transition on both `Produced(value)` and
`SamplingFailed`. A failed attempt performs the construction's exact
failed-state update and, when its failure effect continues, is present in all
later exact prefixes. Only the `Produced` branch creates a `PublicValue`
observation and challenge-value knowledge.
Removing or withholding the later theorem/model basis does not remove any
input to target admission. A subsequent `FSCompile` request returns
`CannotAnswer(missing semantic model and theorem/rule)`, and dependent property
transport is likewise unavailable at its own boundary.

**Identity effects.** Source and target share `c` but have distinct Protocol
IDs because `FreshPublicCoins` and `FiatShamir(TranscriptConstructionId)` are
different interpretation tags. Removing a later theorem basis changes neither
ID.

**Capability and replay effects.** `cap(T)`, target admission, and affirmative
`CheckedFSConstruction Kfs` are distinct. Replay reauthenticates the source with its
Fresh preimage and dependency-authentication capability bundles and the target
with exact `Bfs` and `AdepFS`, reconstructs new retained transcript dependency
views, reacquires exact `Ltarget`, calls the exact four-input `AdmitProtocol`
under `NoCompositionContext`, and reruns
`FinalizeFSConstruction(..., rhoFS)`; no theorem capability is synthesized.

**Preserved nonclaims.** Target admission and affirmative
`CheckedFSConstruction` establish no
random-oracle theorem, soundness, knowledge, zero knowledge, loss bound, or
property preservation. They also establish no induced target-distribution or
correlation theorem beyond the construction's directly checked occurrence and
action maps.

**Decisive falsifier.** FS target admission depends on an ambient theorem
registry, theorem removal invalidates the admitted target, or construction
maps are accepted as `FSCompile`.

### F2 — two property transports over one construction

**Status:** Pass at the Stage 3 separation boundary; Stage 3 intentionally owns
no affirmative property conclusion.

**Declared immutable inputs.** Hold the exact admitted `PF`, FS target `Pfs`,
and affirmative `CheckedFSConstruction Kfs` fixed. Form two immutable request
descriptions, not authority-bearing bases. Each description explicitly names
that shared source/target/construction context and the exact `FSCompile`
judgment required by its property transport:

```text
FA = required FSCompile judgment over
     (PF, Pfs, Kfs, semantic model MA, theorem/rule TA,
      FS assumptions AFA, quantitative parameters QFA)
FB = required FSCompile judgment over
     (PF, Pfs, Kfs, semantic model MB, theorem/rule TB,
      FS assumptions AFB, quantitative parameters QFB)

TransportA = (PF, Pfs, Kfs, FA, source property judgment ref JA,
              property-specific rule ref RA, assumptions AA,
              parameters QA, loss LA, desired target conclusion KA)
TransportB = (PF, Pfs, Kfs, FB, source property judgment ref JB,
              property-specific rule ref RB, assumptions AB,
              parameters QB, loss LB, desired target conclusion KB)
```

No live source-property judgment, applicable semantic-model/theorem preimage,
`FSCompile` judgment, property-specific rule capability, or target property
result is supplied for either request.

**Initial subject and authority state.** Protocol and structural-construction
capabilities exist. No Analysis-owned model, rule, `FSCompile`, or property
result is in Stage 3 authority.

**Operation and exact result.** The two descriptions enumerate complete
desired request keys, but neither is a complete authoritative invocation. The
later-owned boundary returns
`CannotAnswer(missing JA, FA, RA, and their exact authoritative bases)` for
`TransportA` and
`CannotAnswer(missing JB, FB, RB, and their exact authoritative bases)` for
`TransportB`. In particular, `Kfs` is not `FA` or `FB`; the checked structural
construction cannot substitute for either missing `FSCompile` judgment. If
Analysis later supplies one complete basis, it may answer only that request;
the other remains independently unavailable. There is no result kind whose
name or authority is global `FS-valid`.

**Identity effects.** Neither request changes `pF`, `ProtocolId(Pfs)`, or the
identity of `Kfs`. Property-result identity, if later justified for a named
consumer, must commit to its full exact request tuple and outcome.

**Capability and replay effects.** A capability for `TransportA` cannot answer
`TransportB`; common source and FS IDs do not widen it. Cross-process replay
must re-establish `PF`, `Pfs`, `Kfs`, and every exact `FSCompile`, source
property, property-specific rule, assumption, parameter, and loss input.

**Preserved nonclaims.** `CannotAnswer` is not a negative security result.
Distinct possible transports imply neither property, and one affirmative later
transport would not imply the other.

**Decisive falsifier.** One undifferentiated construction or `FS-valid`
capability discharges both requests, or either result omits its exact property,
basis, assumptions, quantitative parameters, or losses.

## 8. Semantic Core composition

### C1 — repeated child and alternative interleavings

**Status:** Pass.

**Declared immutable inputs.** Use two slots, `0` and `1`, both naming `c` and
supplied at spec admission by two ordered uses of the attenuated Core view
derived from `cap(PF)`. Each slot has one `LocalTypedFaceMap` whose port map is
total. Every child input uses `ExternalInput` to a distinct slot-specific
target input with identical direction, role class, visibility, value domain,
`ExactlyOne` multiplicity, and semantic purpose, and maps
`PortValue(child_port, 0)` to exactly `PortValue(target_port, 0)`. Every child
output uses `ExternalOutput` to a distinct slot-specific exactly-one target
output with the same face fields. Its binding is exactly
`ExternalOutput(target_port, [mapped_value])`, where `mapped_value` is the
exact typed image of child `OutputValues[0]`; the target port binds that same
singleton sequence. There is no intentional face
identification, truncation, broadcast, or ordinal permutation. Each child role
maps deterministically to the unique target role of the same class. Equal
child IDs therefore do not identify occurrences. The causal-seam set is empty.
The `locally_added_causal_edges` set is also empty; this fixture introduces no
discretionary ordering edge beyond derived mapping and policy edges.
For this scenario, `c` also declares one private prover-randomness bundle so
both public and private randomness policy families are exercised, and its
public-challenge randomness and private randomness are each
`IndependentFresh`. The authenticated public and private
`DistributionContract`s have exact supports and explicitly permit
`SamplingFailed` in their one-attempt outcome relations; every exercised
`Produced` replay value is in the corresponding exact support. Its public challenge-sampling failure has
`Terminate(the child Abort terminal)` effect.
The only terminating non-challenge failure captured in this fixture is the
check's exact `CheckRejected` occurrence, whose original effect is
`Terminate(the child Reject terminal)`. The class/result pair therefore obeys
`TerminatingResultForFailureClass`. No `ExplicitProtocolAbort` failure occurs
in the captured subdomain; the child's explicit Abort route is an ordinary
`ReachTerminal` occurrence. Every original or propagated terminating failure
in the fixture maps `MalformedProtocolInput` and `CheckRejected` only to
`Reject`, and `ChallengeSamplingFailed` only to `Abort`; none selects
`Accept`.
This C1 fixture declares no claims or reductions, and its check has
`claims = []`. The initial and every post-live-event least-`ReductionRef`
saturation are therefore empty, check-time linear-claim consumption is
vacuous, and no terminal can close with a live linear claim.
For every captured failure or reach source, direct recomputation therefore
establishes exact `CaptureClaimQuiescent(child, source)`: no replacement can
newly satisfy an `AfterEvent` production, no linear claim is live at the exit,
there is no unfired child reduction that could later become enabled, and no
mapped, shared, or locally added target reduction can consume a retained child
claim. All four conditions are vacuous in this explicitly claim- and
reduction-free fixture rather than assumed from suffix suppression.
Every captured non-challenge failure or captured reach point occurs only after
all same-slot Prover- and PublicEnvironment-acted events; every later
same-slot potential event is Verifier-acted. No suppression flag therefore
needs an implicit cross-role publication.

The spec fixes one complete `OrdinaryOriginMaps`. Across both slots it maps
every ordinary child value, object, event, claim, reduction, and check in the
target model's exact domains injectively to a distinct local target ordinal,
preserving each constructor and recursively mapped operand/reference. It does
not claim the port-, randomness-, challenge-, failure-, or terminal-owned
origins excluded from those domains. Each ordinary event preserves its exact
kind, actor, inputs, protected observations, and `obligation_basis`; its only
guard change is the one central suffix-suppression equation stated below. The
terminal-origin map below owns child terminal provenance. The disjoint
`locally_added` set contains every and only declaration with no child or
derived-policy origin, including the
child-disposition domains and complete combiner/result/output routing
structure; policy-owned capture statuses and injections are not duplicated in
it. Every policy-owned suppression formula is materialized as a canonical
`GuardDecision(CanonicalGuardFormula)` value and kept, with its derived edges,
in the policy origin classes. Underlying `FailureOccurred` values remain
non-guard Boolean sources and are not duplicated. Its only local exit
declarations are the
three exact combiner terminals and their three `ReachTerminal` events; it adds
no randomness/challenge bundle, check, failure or failure-origin value,
`RaiseFailure`, or other terminal surface. Roles, ports, dependencies, bundle
policies, failure/reach/terminal-origin policies, recomputed obligations,
ordinary maps, and `locally_added` jointly cover every target declaration
exactly once.

The target causal-edge set is exactly the union of every child-edge image
under the complete occurrence maps and the deterministically recomputed
face-feed, challenge/private-randomness, failure/reach-rewrite,
suffix-suppression, and terminal-combiner edges. The seam and locally-added
edge classes contribute their declared empty sets. The classes are disjoint,
the union is acyclic, and neither target fragment contains an arbitrary edge
or omits a derived one.

Both spec candidates use target regime `rhoP`, and every ordered child Core
view has exactly that same `ProtocolSemanticRegimeId`; each supplies one
complete local target fragment. Cross-regime composition is unavailable in v0
without a future explicit semantic-translation subject and checked relation.
Each challenge-policy entry is `IndependentChallenge` and
maps the child's entire linked challenge bundle to a distinct
`LocalTargetFreshChallengeBundle`, including the event, value, randomness,
public-sampling obligations, sampling failure, an index slot, and
`IndependentFresh` correlation declaration. The target event, value,
randomness, failure, obligation backlinks, and distribution are the exact
typed image of that child bundle. The target `RandomnessDecl` referenced by
`bundle.randomness` has a `distribution` field that is an exact
`LocalTargetDistributionContractRef`, equals the child distribution under the
typed image, and is backed by the corresponding authenticated preimage in the
child/local pool; it is not a global or live contract reference in the spec.
The child integer `public_coin_index` is
not preserved: the target index is recomputed as that target `FreshChallenge`
event's zero-based rank in the chosen target interleaving. The checked maps
retain child challenge occurrence and child index to target occurrence and
that recomputed target index. The event retains the exact
`FreshChallengeContracts(resolve)` basis, the corresponding
`ResolvePublicChallenge` endpoint obligation is deterministically recomputed,
and its challenge-prefix template
is the exact recomputation under the target schedule. As a
PublicEnvironment-acted Fresh event, its `prover_construction` field is absent.
Each private-randomness entry uses
`PreserveIndependent` with a distinct complete target bundle, preserving its
value origin, owner obligation, private-sampling nonproduction failure,
distribution through the corresponding `LocalTargetDistributionContractRef`,
and `IndependentFresh` correlation.

The two target public-challenge bundles and two target private-randomness
bundles use four distinct `RandomnessRef`s. A structurally valid
`RandomnessReplay` contains one record for each and only dynamically attempted
Fresh-challenge or private-randomness occurrence, ordered first by Core
schedule and then by the prover obligation's identity-bearing basis order.
Every next record must name the exact randomness and source event and carry a
contract-admissible produced value or the exact
`IndependentSamplingFailed` replay constructor; a guarded
unattempted occurrence consumes no record. Each public target `ChallengeDecl` has the unique
one-to-one randomness backlink, and its `public_coin_index` is exactly its
zero-based `FreshChallenge` rank in that candidate's total target schedule.
There are no joint groups; common child types and repeated child ordinals
therefore create neither sharing nor correlation.

The terminal combiner names `Dterm` as an exact
`LocalTargetValueDomainContractRef = terminal_result_value_domain`. Its local
target dependency declaration is backed by the authenticated finite-domain
preimage in the local/child pool. Its canonical inhabitants are exactly
`CanonicalTerminalResultValue(Accept)`,
`CanonicalTerminalResultValue(Reject)`, and
`CanonicalTerminalResultValue(Abort)`, with no other inhabitant, and
`result_domain = {Accept, Reject, Abort}`. Every captured terminal-result
constant and every combiner comparison uses this same contract.

`failure_policy` is total over child verifier-visible failure occurrences.
This fixture has no already-continuing child failure, so the
`PreserveContinue` subdomain is empty. Every terminating non-challenge failure
in the captured subdomain is the exact `CheckRejected` occurrence above and
uses `CaptureFailure` into a slot-specific target failure whose effect is
`ContinueWithStatus`, together with its exact
`FailureStatusValue`, complete captured-exit value, and suppression map. The
status value's runtime payload is only the canonical
`FailureStatusToken {target failure, target class}`; the captured-exit value is
exactly `Tuple(FailureStatusValue(target failure),
CanonicalConstant(Dterm,
CanonicalTerminalResultValue(child terminal result)), mapped child terminal public
outputs...)` in that order. Its mapped observation set is the child's set with
`Terminal` removed. Each nonremoved target failure has the exact typed image
of the child source and backlinks and the same failure class. Each fresh
challenge's sampling failure is the one named by its target challenge bundle
and has a matching
`PropagateFailure` entry to an `Abort` terminal whose result and public outputs
are the exact typed image of the child failure terminal. The target failure's
effect is exactly `Terminate(the mapped Abort terminal)`, and its mapped
failure observations are exact. At every such failure selector, the complete
ordered Abort payload is already semantically available and known to the
Verifier at that exact transition; it depends on neither the failed and thus
unproduced challenge value nor any later or continuing-only value. No
`RemovedByChallengeSubstitution` entry is needed because this fixture derives
or imports no challenge.
An `ExplicitProtocolAbort`, were one present, could appear only under
`PropagateFailure` to an `Abort` terminal; placing that class under
`CaptureFailure` or `PreserveContinue` makes spec admission negative.

`reach_exit_policy` is total over child `ReachTerminal` occurrences. Every
entry uses `CaptureReach` into a slot-specific raw status value that is exactly
`Tuple(CanonicalConstant(Dterm,
CanonicalTerminalResultValue(child terminal result)), mapped child terminal public
outputs...)` in that order. Its enclosing sum variant identifies the exact
child reach occurrence, so the payload contains no duplicate ambient
occurrence label. Its replacement is exactly a verifier
`ObservePublicValue(status)` event with the mapped original guard conjoined,
when applicable, with suppression of every earlier captured exit, exact input
list `[status]`, and protected observations exactly equal to the mapped child
set with `Terminal` replaced by `PublicValue`. It has the one kind-exact
`ObservePublicValueContracts` basis and its endpoint obligation is
deterministically recomputed; because the capture observation is verifier
acted, its `prover_construction` field is absent. Every captured reach or
failure carries a total
`SuffixSuppression`: for a captured failure, `exit_taken` is exactly
`FailureOccurred(target failure)`; for a captured reach, it is exactly the
final mapped reach-guard contribution after suppression by any earlier capture.
Every later event origin contributes its mapped source guard or policy-specific
base guard conjoined with the negation of the disjunction of all earlier
captured-exit flags for that slot. Each conjunction, disjunction, or negation
is reduced by `rhoP`'s fixed reduced-ordered-decision-diagram algorithm into
the exact `GuardDecision`, and the resulting contribution is a
`GuardValueRef`. Every mapped event in this independent
fixture has one origin, so its final target guard is exactly that one
contribution; no many-to-one shared-challenge coactivation equality is invoked.
For each later event, every captured-failure Boolean is resolved even when its
source did not fail or was inactive, and is
`AvailableAt(Verifier, flag, PreAttempt(later_event))`. Every captured-reach
flag is built from guard operands already known to the Verifier actor and is
available at the same boundary. Thus that later Verifier event knows every
atom in its rewritten activation guard.
Consequently an ordinary child exit continues to the other slot without
permitting any post-exit suffix of the first slot to become active; a
challenge-sampling failure instead follows the explicit propagated abort.

`terminal_origin_map` is total for every terminal in both child occurrences.
Every disposition's `removed_sources` is empty because this fixture performs
no derived or imported challenge substitution.

For each slot's child `Abort` terminal, `mapped_target` is one distinct
slot-specific target Abort terminal because the challenge-sampling failure is
propagated; its `captured_sources` is exactly every other terminating failure
or `ReachTerminal` occurrence targeting that child terminal. For every other
child terminal, `mapped_target` is absent and `captured_sources` is the entire
set of its terminating failures and reach occurrences. Thus each noncaptured
source uses the matching `PropagateFailure`, every propagated source for one
child terminal names its one exact typed target image, and target images of
distinct child terminal occurrences are injective. The three terminal-combiner
finals are separate `locally_added` terminals, so every target terminal has
exactly one mapped or local origin.

`TotalTerminalCombiner` contains exactly two `CombinerInput` records in
canonical child-slot order, one for slot `0` and one for slot `1`; each record's
`merged_status` is one exhaustive one-hot `GuardedMerge`. Each slot declares one
canonical child-disposition sum domain as an exact
`LocalTargetSumValueDomainContractRef`
with one distinct variant for every captured reach-status tuple and complete
captured-failure-exit tuple, ordered by the corresponding child exit
occurrences.
Every `CaptureReach` and `CaptureFailure` carries an `ExitStatusInjection`
whose `raw_status` is exactly its complete captured-exit value, whose distinct
declared variant has that exact payload domain, and whose `injected_status` is
exactly
`InjectVariant(child_disposition_sum, variant_ordinal, raw_status)`. These
injected values—not the heterogeneous raw statuses—are the branches; each is
guarded by the corresponding exact final suffix-suppressed reach-guard
contribution, or for a captured failure by
`GuardDecision(BooleanAtom(FailureOccurred(target failure)))`. The
`GuardedMerge` therefore has a common domain while preserving the exact status
kind and payload, and every captured status contributes exactly once. At
runtime all branch guards resolve, exactly one is true, and only that selected
injected status must be available; unselected branch values need not be
produced. The
combiner's explicit result value equals
`Apply(result_function, [inputs[0].merged_status,
inputs[1].merged_status])`; `result_function` is an exact
`LocalTargetPureFunctionContractRef`, total with codomain `Dterm`, its
range contains only the canonical values for `result_domain`, and it applies
precedence
`Abort > Reject > Accept`. Each final-map entry sets
`public_output_function = result_output_function`, the same exact total pure
`LocalTargetPureFunctionContractRef` mapping the complete ordered merged-status
tuple to the one-field product containing the computed result. Both function
refs and every sum-domain ref are backed by their exact authenticated
preimages in the local/child dependency pool. Its
`public_output_tuple` is exactly
`Apply(public_output_function, [inputs[0].merged_status,
inputs[1].merged_status])`, its `public_output_values` is exactly the
one-element canonical sequence containing projection `0`, and its terminal
declares exactly that value as its sole public output. The `finals` map has
three distinct static `TerminalDecl`s with matching results and three
`ReachTerminal` events: the exact
`GuardDecision(FiniteValueEquals(result_value,
CanonicalTerminalResultValue(Abort)))` and
`GuardDecision(FiniteValueEquals(result_value,
CanonicalTerminalResultValue(Reject)))` guards, followed by
`UnguardedFallback` for `Accept`, materialized as the canonical true guard, in
`route_order = [Abort, Reject, Accept]`. Exactly one result-and-output route
action occurs for each result because `ExecutionStillLiveBefore` suppresses that
fallback after either earlier route has selected its terminal. Each final
route also satisfies the checked completion/order formulas. On every path
where `ExecutionStillLiveBefore` holds at the first final, each of the two
slots has completed at exactly one captured source and each slot's
`GuardedMerge` selects exactly one branch, so there is exactly one combiner
input per slot. Every event resolving a captured or propagated child terminal
precedes every final in both the recomputed causal-edge set and the chosen
interleaving, and the three finals follow `route_order`. For each final,
`EventAttempted(final)` implies that no propagated exit was selected, exactly
one captured completion is available for each slot, and both
`inputs[*].merged_status` values are available. The no-input/
mandatory-propagated-exit alternative is vacuous because both slots have a
combiner-reaching capture path in this fixture. Each final
event has the kind-exact
`ReachTerminalContracts` basis and its endpoint obligation is deterministically
recomputed. Its exact kind equation is
`final_event.inputs = final_terminal.public_outputs =
final.public_output_values`, its protected observations are exactly
`{Terminal}`, its actor is the Verifier, and its `prover_construction` field is
absent.
The local fragment declares every
port/value/challenge/randomness, status, underlying non-guard Boolean source,
`GuardDecision` guard, merge/result/output value,
capture/final event, failure, terminal, endpoint/prover obligation, and
prover-obligation-failure declaration used by the rewrite. Capturing child
exits is an explicit intentional change, not a preservation claim.

Path-sensitive role knowledge is closed explicitly. On every captured source
path, the verifier knows the original terminal's ordered public outputs before
the replacement and therefore knows the complete capture-status input to its
`ObservePublicValue` event and that path's selected injected status. All merge
guards resolve; the verifier need not know unselected branch values. It knows
the resulting merged status, combiner result, and projected output on every
active final route, so every capture and final event input is available at its
exact schedule point.

Target dependencies are the deterministic least reachable closure from the
fully rewritten target's typed dependency roots, drawn from the exact child
and locally supplied preimage pool. Those roots include the named status and
child-disposition sum domains, `Dterm`, result function,
result-output function contract,
exact `ObservePublicValueContracts` contract for the capture replacements, and
exact `ReachTerminalContracts` contract for the combiner finals. A child-only
contract whose last target use was eliminated by capture is not retained as
historical target semantics. Reachable equal entries from the repeated child
merge only because kind, regime, content identity, preimage, and ABI all match.
Endpoint obligations, prover obligations, and
prover-obligation failures are recomputed from the fully constructed target
events and randomness, and the local fragment contains exactly those
recomputed sets.

Each candidate is accompanied by the sole exact dependency-authentication
pair.
`Bspec : ExactCompositionSpecDependencyPreimageBundle` contains every and only
preimage declared by `target_fragment.dependencies`, including declarations
also available through a child view, under the full typed local key; `Aspec`
is its exact kind/regime/ID/ABI/direct-edge-matched
`ExactCompositionSpecDependencyAuthenticationCapabilities` set.
Authentication retains attenuated target dependency views for this complete
bundle. At admission, the target least required key closure must equal this
bundle exactly. For each key, reachable child-origin views are deterministically
deduplicated only on exact preimage/ABI/direct-edge equality. Only when no
reachable child supplies the key may the authenticated spec-retained target
view supply it, and that ref must be covered by `locally_added`; local supply
cannot shadow a reachable child origin. Unreachable child history is ignored.
The selected child/local views must equal the authenticated target bundle
exactly. Live preimages, attenuated views, and checker capabilities are
operation authority and do not enter `CoreCompositionSpecId`.
For each candidate, fix exact `ExactCoreAdmissionCheckerCapabilities Ecore`
matching `rhoP` and every exact selected admitted target dependency view
retained by that spec. `Ecore` is a direct formation input used only for
`CoreAdmissible`; it is not retained in the spec, target identity, or completed
result.

Two spec candidates hold every discretionary child map, policy choice,
contract, and route rule fixed while selecting different valid total
interleavings; call their raw forms `S01raw` and `S10raw`. Because public-coin ranks and challenge-prefix templates are
schedule-derived identity-bearing fields, each candidate stores their exact
recomputation and the resulting derived causal-edge closure for its selected
schedule; those necessary consequences, rather than an ambient repair, differ
with the interleaving. Each schedule is a
permutation of every and only event in the complete local target fragment.
`sigma01` schedules all mapped potential body events and capture replacements
of slot `0` before those of slot `1`, then the three potential combiner-route
events; `sigma10` reverses the two slot blocks and then uses the same ordered
routes. Consequently the slot `0` and slot `1` public-coin ranks are
respectively `(0, 1)` in `sigma01` and `(1, 0)` in `sigma10`; each stored prefix
is likewise the exact schedule-ordered sequence of prior potentially
action-occurring transcript-participating target
`EventActionOccurrenceRef`s—exactly transcript-observed and challenge
events—with their derived predicates retained. It contains no nonparticipating
event merely because that event precedes the challenge.
Under the complete child-to-target event relation, including capture
substitutions, both extend every child schedule, every child causal edge, and
every seam.
For each subsequently admitted Fresh target and exact execution trace, fix
`Eexec : ExactProtocolExecutionCapabilities` whose `core_dependencies` map
contains every and only content-addressed dependency actually evaluated by
that trace, matched to its admitted view by kind, regime, content ID, ABI, and
direct edges, and whose `transcript_algorithms = None` exactly.
Then
`ExecuteProtocol(admitted_target, CoreInvocationInputs, ProverTrace,
RandomnessReplay, Eexec)` with structurally valid invocation inputs, a
canonical trace, an exact dynamically matched replay, and no residual prover
or randomness records has the following behavior. Paths without a propagated
public-challenge sampling failure use the exact guards and suffix-suppression
values to leave only each child's pre-exit prefix action-occurring, scan both
slots, and reach exactly one combiner `ReachTerminal`; a legal failed
public-challenge attempt reaches
its exact propagated abort terminal and bypasses the combiner. The exact
recomputed producer-failure family instead yields `ProverDidNotProduce` for
the first `EarlyOutput`, `DuplicateOutput`, `UnexpectedOutput`,
`MissingOutput`, or explicit attempted-private-randomness
`IndependentSamplingFailed` record. A missing, reordered, mismatched, or extra randomness record is
`Malformed` and mints no Core outcome. A reached `Accept` terminal with
residual prover records does not satisfy `AcceptProtocol`. A missing, extra,
or mismatched execution capability is `Refused`; operational evaluator failure
is `CheckerFailure`, and neither mints a Core outcome.

**Initial subject and authority state.** The spec candidates contain only
`CoreId` values and typed local child/target references. They carry no child or
target authority and no self-reference. The caller has `cap(PF)` and can derive
the two ordered child Core-view inputs, and has exact `Bspec`, `Aspec`, plus
the matching `Ecore` for each raw candidate; neither
authenticated/admitted spec authority nor target authority exists.

**Operation and exact result.** For each candidate `Sxraw`,
`AuthenticateCoreCompositionSpec(raw_spec, Bspec, Aspec)` checks closed local
form and the every-and-only complete declared dependency bundle, retains its
attenuated views, and mints an authenticated candidate with a distinct
`CoreCompositionSpecId`; only then are
`ChildOccurrenceRef(spec_id, 0)` and `ChildOccurrenceRef(spec_id, 1)` formed.
The identity preimage orders the fields exactly as `children`, `face_maps`,
`ordinary_origin_maps`, `terminal_origin_map`, `locally_added`, `causal_seams`,
`locally_added_causal_edges`, `interleaving`, `challenge_policy`,
`private_randomness_policy`, `failure_policy`, `reach_exit_policy`,
`terminal_combiner`, and `target_fragment`, after the composition and target
Protocol regimes.

`AdmitCoreCompositionSpec(authenticated_spec, ordered_child_views)` consumes
only the authenticated spec and exact ordered live child views. It checks that
every child regime equals the spec's target `rhoP`, recomputes the exact target
required-key closure, and requires it to equal the authenticated retained
bundle. It selects only origin-reachable child views, merges equal full typed
keys only on exact preimage/ABI/direct-edge equality, uses a retained target
view as local supply only for a required `locally_added` key that no reachable
child supplies, forbids local shadowing, and ignores unreachable child history.
A missing, extra, conflicting, or mismatched dependency, preimage, edge, view,
regime, or authentication capability is refused rather than recovered
ambiently. Admission then checks every total face map,
ordinary-origin map, terminal-origin map, origin
partition, exact causal-edge partition and locally-added-edge set, challenge
and private-randomness bundle, fragment reference, interleaving, failure
policy, reach-exit policy, suffix-suppression map, guarded merge, and total
combiner route. Call the resulting admitted specs `S01` and `S10`. For each
admitted `Sx`, form its matching admitted target `Px`:

```text
ConstructAndSubadmitCore(admitted_spec, Ecore)
  -> CanonicalCoreCandidate
     + transaction-scoped CoreAdmissionWitness
     + transaction-scoped ScopedCompositionFormationAuthority
FormAndAdmitProtocol(CanonicalCoreCandidate, witness, FreshPublicCoins, rhoP)
  -> admitted target Protocol
FinalizeCoreComposition(Sx, Px)
  -> Affirmative(
       CheckedCoreComposition KCx carrying
       CoreCompositionCheckedPayload.Affirmative(
         Mx: ResolvedCoreCompositionMaps))
```

`Ecore` is consumed only by the Core-admissibility subcheck and is not retained.
This Fresh target does not consume the scoped formation authority for
transcript-construction admission; it is discarded with the Core witness and
unforgeable formation-invocation token when the transaction closes. Neither can
escape. Finalization derives the target Core view and internally runs the pure
total `ResolveCoreCompositionMaps(admitted spec, admitted target Core view)`.
The resulting `KCx` retains the unique immutable
`ResolvedCoreCompositionMaps Mx`,
including every same-kind ordinal-preserving target-reference bijection, every
resolved policy/origin map, and all five deterministically recomputed derived-
origin maps. No caller-supplied or serialized raw map enters finalization or
grants authority.

Now deliberately cross the already admitted exact operands:

```text
FinalizeCoreComposition(S01, P10)
  -> Negative(
       CheckedCoreComposition KN carrying
       CoreCompositionCheckedPayload.Negative(
         mismatches = N01x10,
         unaffected_agreements = A01x10))
```

`N01x10` is a nonempty canonical set of typed
`CoreCompositionComparisonFact`s. It includes the exact
`SubjectIdentity(CoreId)` fact with expected `CoreId(P01)` and actual
`CoreId(P10)`, plus the exact
`ResolvedField(TargetInterleaving, ordinal 0)` fact with the expected first
slot-`0` target event reference and actual first slot-`1` target event
reference; `A01x10` retains the exact
equal child IDs and slots, regimes, face maps, and every unchanged policy
equation. `KN` retains the exact admitted child views, target attenuated view,
composition regime, nonempty mismatch facts, and unaffected agreements. It
retains no `ResolvedCoreCompositionMaps` and cannot inhabit
`CompositionContextAuthority`. The cross-pair is a completed semantic
negative, not malformed input, refusal, checker failure, or a partial map.

Because the total schedule is identity-bearing and transcript-observed, the
two target canonical Core encodings and `CoreId`s differ. In each result,
ordinary nonterminal occurrences from equal child IDs remain injectively
distinguished by slot; child exits map through the exact slot-specific status
substitutions and one of the three equality-guarded/fallback final routes.
Independent child challenge and private-randomness bundles map injectively to
distinct complete target bundles.

**Identity effects.** Equal child IDs do not collapse occurrences. Different
interleavings produce different spec IDs and, in this fixture, different
target Core and Protocol IDs. A future pair of histories that normalizes to an
identical intrinsic target Core may share a target `CoreId` while retaining
distinct spec IDs and checked provenance. The cross-pair check changes no
identity; its negative capability is bound to the existing `S01` and `P10`
identities.

**Capability and replay effects.** A spec ID does not authorize either child or
target dependency. The admitted spec retains the exact admitted child views and
exact selected attenuated target dependency views through subadmission;
each affirmative `CheckedCoreComposition KCx` additionally retains the
target's attenuated view and `Mx`. The negative `KN` retains the exact child
and target views and typed facts but no resolved map or context authority.
Replay re-authenticates the complete `Bspec` with newly
reacquired `Aspec`, re-admits the children, and reruns two-input spec admission
only after recomputing required-key closure, reachable-child selection,
same-key equalities, local-supply eligibility, nonshadowing, and final
coverage. It separately calls
`AuthenticateCanonicalPir_rhoP(persisted target raw, Bcold, AdepCold)`, where
`Bcold` contains every and only target Core dependency preimage and
`transcript_construction = None`, and
`AdepCold = {core = exact same-key map as Bcold.core_dependencies,
transcript = None}`. Cold reopen then calls
`ReplayAndAdmitComposedProtocol(authenticated persisted target candidate,
freshly admitted exact spec, ExactProtocolAdmissionCheckerCapabilities)`. The
capability bundle contains every and only checker for the exact Core
dependencies and has its transcript-construction checker component absent,
because this target is Fresh; a missing, extra, or mismatched capability is
refused. The operation reruns
`ConstructAndSubadmitCore`, requires exact equality of the reconstructed Core
body, target regime, and `CoreId` with the authenticated persisted candidate,
follows the equality path without consuming transcript-construction authority,
admits the target, and reruns two-input finalization to recompute the exact
`ResolvedCoreCompositionMaps` and mint a new affirmative
`CheckedCoreComposition`. No prior
scoped witness, formation authority, or serialized composition result crosses
the boundary.
Replaying the cross-pair separately re-admits `S01` and `P10`, reruns
two-input finalization, and mints a fresh negative `KN`; neither its durable
facts nor its checked capability can be replayed as maps or context authority.

**Preserved nonclaims.** Neither structural result proves associativity,
commutativity, idempotence, security-property composition, child property
preservation, or `FS(compose) = compose(FS)`. The capture policy deliberately
changes standalone first-terminal behavior and claims no trace preservation.
The negative cross-pair refutes only the exact checked composition equations;
it does not make either admitted operand malformed or refute their independent
Protocol meanings.

**Decisive falsifier.** Equal child IDs collapse slots; `Bspec` is narrowed to
only local dependencies; repeated reachable child dependency keys are rejected
without exact-equality merging, conflicting equal keys are silently merged,
local supply shadows a reachable child origin, unreachable child history causes
a conflict, required bundle coverage is not checked exactly, or a child regime
differs from `rhoP`; a spec-field change
fails to change `CoreCompositionSpecId`; a resulting target-semantic change
fails to change `CoreId`; a spec hashes its own global occurrence refs; or a
child exit occurrence, captured suffix, private-randomness source, or complete
challenge bundle is left without a total policy; a face map is partial; an
ordinary-origin map is partial or noninjective; a target declaration has zero
or two origin classes; a schedule-derived coin index or challenge prefix is
ambiently repaired; a derived causal edge is missing or an arbitrary
fragment-only edge lacks `locally_added_causal_edges` provenance; a dynamic
compound result does not select exactly one matching static terminal with its
exact pure public-output tuple and ordered projections; or a composition
capability exists before target Protocol admission; or caller-supplied or
serialized resolved maps grant authority.
An additional falsifier is a negative checked composition carrying resolved
maps, authorizing composed transcript admission, losing unaffected agreement
facts, or being collapsed into refusal, malformedness, or checker failure
despite exact admitted operands.
Different specs may retain one `CoreId` when their intrinsic target Core is
identical.

### C2 — graph union, static link, and certificate adjacency

**Status:** Pass.

**Declared immutable inputs.** Construct three proposals from the same child
IDs: a static linker output with unresolved face aliases; a graph union that
omits a total interleaving, complete face/ordinary-origin/terminal-origin/
challenge/private-randomness maps, exact declaration-origin and causal-edge
partitions, a locally-added-edge set, failure and reach-exit policies, suffix
suppression, guarded merge values, terminal-combiner routes, and a complete
target fragment; and two checked certificates placed next to each other
without a semantic composition relation.

**Initial subject and authority state.** Child Protocols may be admitted, but
all three composition attempts are authoring material. None is an admitted
`CoreCompositionSpec` or `CheckedCoreComposition` result.

**Operation and exact result.** The incomplete graph-union candidate is
`Malformed(missing total interleaving, ordinary/terminal origin maps and
exhaustive declaration/causal-edge partitions, locally-added edges, policies,
terminal combiner, and target fragment)` as a composition spec. Offering only
the static-link output to the composition boundary is
`Refused(missing admitted composition spec and exact live child views)`; the
link output remains an
unauthoritative proposal until its aliases, faces, seams,
ordinary and terminal origins, declaration partition, causal-edge provenance,
dependencies, failures, and obligations are converted into and checked as a
complete spec. Certificate adjacency is
`Unsupported(not a CoreComposition relation)`.

A linker may independently emit a physically canonical target Protocol that
later admits. That fact still mints no `CheckedCoreComposition`; target
admission is not provenance or a checked child-to-target relation.

**Identity effects.** Proposal digests, link output IDs, or adjacency have no
composition authority. An independently admitted target has its intrinsic ID
only.

**Capability and replay effects.** Child capabilities do not combine by
co-location. Only the full spec, live child views, admitted target, and map
recomputation can mint `CheckedCoreComposition`.

**Preserved nonclaims.** Refusing the composition claim does not say the linked
target is malformed or useless; it says the claimed semantic relationship has
not been checked.

**Decisive falsifier.** Static symbol resolution, graph union, a common parent
package, or certificate adjacency alone mints `CheckedCoreComposition` or
property authority.

## 9. Structural relation, persistence, and OIR boundary

### T1 — structural success without property transport

**Status:** Pass.

**Declared immutable inputs.** Reuse one affirmative
`CheckedCoreComposition KC` trace from `C1`, including exact admitted child and
target views, the admitted spec, and its retained
`ResolvedCoreCompositionMaps`. The exact composition regime is committed
through the admitted spec; historical formation checker `Ecore` is not
retained by `KC`. Fix one
exact later-owned supported request `Qsound` to transport
a named soundness judgment from those exact children to that exact target under
Analysis regime `rhoA`. Supply neither the named source soundness judgment nor
the applicable property-composition/transport rule.

**Initial subject and authority state.** All structural capabilities are live.
No source property judgment or property rule exists.

**Operation and exact result.** Exact
`FinalizeCoreComposition(admitted spec, admitted target)`
returns a fresh affirmative `CheckedCoreComposition KC2` within its structural
scope. The exact `Qsound` request returns
`CannotAnswer(missing named source soundness judgment and applicable
composition/transport rule)`.

**Identity effects.** Structural success changes no subject identity. A later
property result, if any, is a separate result over additional inputs.

**Capability and replay effects.** Neither `KC` nor `KC2` can be cast or
widened into an Analysis capability. Serialization requires exact composition
replay and finalization to mint a fresh local `CheckedCoreComposition` and
still supplies no property authority. A cold reconstruction path reacquires
an identity-matched `Ecore` to reconstruct and subadmit the target; direct
two-input re-finalization over already admitted operands neither reads nor
recovers that historical checker.

**Preserved nonclaims.** No soundness, completeness, knowledge, zero knowledge,
distributional, or cost conclusion follows.

**Decisive falsifier.** A property consumer accepts the structural result alone
or a shared result tag makes structural and property authority
interchangeable.

### S1 — serialization and process reset

**Status:** Pass.

**Declared immutable inputs.** In process `A`, serialize canonical material
for admitted `PF`, `I`, `PlanA`, `RI`, artifact profile `phi`, adapter `A`,
`RB`, exact raw artifact bytes, artifact observation `Om`, a durable comparison
record corresponding to process-`A`'s live
`CheckedArtifactInterfaceComparison Am`, and a durable correspondence record
justified by the named
process-`B` consumer. The durable record binds every subject ID and regime,
the exact `CorrespondenceQuestion`, artifact-observation and comparison inputs,
checker identity, exact qualified outcome, retained facts, and residual trust.
Also serialize strings claiming that every process-`A` capability was
admitted.

Fix the complete process-`B` replay inputs independently of those strings:

- `BPF`,
  `AdepPF = {core = exact same-key map as BPF.core_dependencies,
  transcript = None}`, resulting `VPF`, and
  `LPF = {core = LcorePF, transcript = None}` for Fresh `PF`;
- `BI`, `AI`, resulting `VI`, and `LI` for `I`, and `BPlan`, `APlan`,
  resulting `VPlan`, and `LPlan` for `PlanA`;
- `DRI : ExactRelationDependencyPreimageBundle`, matching
  `ARI : ExactRelationDependencyAuthenticationCapabilities`, resulting
  retained exact relation-dependency views `VRI`, and
  `LRI : ExactRelationInterfaceLawCheckerCapabilities` for `RI`;
- `Dphi : ExactRelationArtifactProfileDependencyBundle`, keyed by
  `TypedRelationArtifactProfileDependencyRef` and containing the exact
  `ExactByteLanguageContractRef` closure, with matching authentication
  capabilities `Aphi`, retained views `Vphi`, and profile law checkers `Lphi`;
- `DA : ExactRelationAdapterDependencyBundle`, keyed by
  `TypedRelationAdapterDependencyRef` and containing the exact
  `ExactDeterministicInterpreterContractRef` closure, with matching
  authentication capabilities `AA`, retained views `VA`, and exact
  interpreter-and-law checker capabilities `LA`;
- `DB1`, `AB1`, resulting `VB1`, and `LB1` for `RB`, plus exact
  `ExactRelationAdapterInterpreterExecutionCapabilities Eobs`; and
- the same exact `PlanRealizesRegime rhoRealizes`, artifact question,
  correspondence question, and `rhoCorr` as the process-`A` results.

Every typed bundle is the every-and-only least reachable closure and retains
kind, contract regime, content ID, exact ABI, and direct dependency IDs.

**Initial subject and authority state.** Process `A` has live local
capabilities. Process `B` initially has only raw bytes and claimed IDs; its
authority set is empty.

**Operation and exact result.** Process `B` first authenticates `PF` with
`BPF = {core_dependencies = every and only member of PF's least Core
dependency closure, transcript_construction = None}` and `AdepPF`, then calls
`AdmitProtocol(authenticated PF, VPF, NoCompositionContext, LPF)`. A missing
Core checker or extra transcript checker is refused. It then runs, in exact
dependency order:

```text
AuthenticateProtocolInterface(I, BI, AI)
AdmitProtocolInterface(authenticated I, exact PF view, VI, LI)

AuthenticateProverPlan(PlanA, BPlan, APlan)
AdmitProverPlan(authenticated PlanA, exact PF plan view, VPlan, LPlan)

AuthenticateRelationInterface(RI, DRI, ARI)
AdmitRelationInterface(authenticated RI, VRI, LRI)

AuthenticateRelationArtifactProfile(phi, Dphi, Aphi)
AdmitRelationArtifactProfile(authenticated phi, Vphi, Lphi)

AuthenticateRelationAdapter(A, exact admitted phi identity view, DA, AA)
AdmitRelationAdapter(authenticated A, admitted phi, VA, LA)

AuthenticateRelationBinding(RB, DB1, AB1)
AdmitRelationBinding(authenticated RB, exact PF binding view,
                     admitted I, admitted RI, VB1, {}, LB1)
```

Each call rejects missing, extra, transitive-closure, typed-key, regime, ABI,
edge, retained-view, or checker mismatches; no dependency or executable is
recovered from a serialized ID or registry. Process `B` then runs
`PlanRealizes(PF, PlanA, rhoRealizes)` and mints a new
`CheckedPlanRealizes`.

It re-supplies the exact raw artifact bytes and calls
`InterpretRelationArtifact(bytes, phi, A, Eobs)` to obtain a fresh completed
candidate with recomputed `RelationArtifactByteId`. It next calls
`AuthenticateRelationArtifactObservation(candidate, bytes, phi identity view,
A identity view)` and
`AdmitRelationArtifactObservation(authenticated candidate, bytes, phi, A,
Eobs)` to mint local admitted observation `OmB`. Only then does it rerun
`RelationArtifactAgreesWithInterface(OmB, RI, exact artifact question,
rhoCorr)` to mint local `CheckedArtifactInterfaceComparison AmB`, followed by
the same `RelationCorrespondsAtInterface(..., AmB, None, rhoCorr)` question to
mint local `CheckedRelationCorrespondenceJudgment JmB`. If the same semantic
material is supplied, the semantic IDs recompute identically, but every
process-`B` subject and result capability is newly minted. The serialized
admitted-marker, result record, and checker-identity strings are ignored as
authority.

**Identity effects.** Semantic identities survive exact re-authentication;
process-local capability identity does not. Changing any bound subject,
regime, checker, observation, or outcome invalidates replay of the durable
result.

**Capability and replay effects.** No capability crosses serialization,
reopen, FFI, or process boundaries by assertion. A mutation becomes a new raw
candidate. The durable record is a replay target, not a live result handle.

**Preserved nonclaims.** Successful replay does not establish provenance,
independent review, deployment validity, witness satisfaction, or a
cryptographic property.

**Decisive falsifier.** Process `B` accepts a serialized admitted marker,
reuses an `A` pointer or handle, skips a subject/result checker, or treats a
matching digest as live authority.

### O1 — local OIR validity without source coverage

**Status:** Pass at the ownership seam.

**Declared immutable inputs.** A later endpoint consumer receives exact OIR
material `O`, its target-local regime and dependencies, but no source
Protocol, Interface, Plan basis, projection result, source map, or
source-bound projection evidence.

**Initial subject and authority state.** The consumer may be able to establish
an OIR-local capability under Stage 4 semantics. It has no admitted source
view and no projection-relation capability.

**Operation and exact result.** `LocalOirValid(O, local_inputs)` may be
affirmative when Stage 4 defines and checks it. The distinct request
`ProjectionCorrect(source, O, relation)` returns
`CannotAnswer(missing source subject and source-bound projection evidence)`.
No Stage 3 owner manufactures the missing source.

**Identity effects.** OIR-local identity or validity does not reconstruct a
Protocol, Interface, or Plan ID and does not create a source-relative
relation.

**Capability and replay effects.** A local OIR capability cannot be widened to
projection authority. Supplying the missing source later starts a new exact
check; it does not retroactively upgrade the old result by assertion.

**Preserved nonclaims.** Local validity does not establish source coverage,
projection correctness, endpoint availability, deployment validity, or
execution success.

**Decisive falsifier.** Any consumer concludes source coverage solely from OIR
shape, local validity, an embedded source ID, or a producer assertion.

## 10. Cross-cutting probes

### 10.1 Hidden-input closure

For each row, all declared inputs are held byte-for-byte and identity-for-
identity fixed while only the suspected hidden input varies.

| Suspected hidden input | Instantiated variation | Required and obtained model result | Falsifier |
|---|---|---|---|
| Resolver or symbol table | Swap two ambient resolver maps | No semantic operation reads either; resolved dependency IDs and preimages in the declared closure control the result | Outcome changes while declared closure is fixed |
| Registry | Add or remove ambient mnemonic operation, adapter, or checker entries while exact declared IDs, preimages, and capabilities remain fixed | Closed Protocol grammar and owner-selected checkers ignore the ambient registry | A string lookup silently selects semantic meaning |
| Carrier printer or bytecode version | Change transport while decoding to the same canonical graph | Same semantic IDs after ordinary physical authentication | Printer spelling or bytecode version enters semantic identity |
| Theorem store | Remove every theorem while holding FS subjects fixed | Protocol and affirmative `CheckedFSConstruction` remain; `FSCompile`/transport are `CannotAnswer` | Protocol admission changes |
| Compiler implementation | Swap compiler binary or optimization policy | No Stage 3 subject or relation reads it | Compiler choice changes Protocol or correspondence result |
| Runtime prover or supplier strategy | Swap the Plan executor and every supplier while holding the same live `AdmittedProtocol` capability, its retained dependency/construction views, exact `CoreInvocationInputs`, `ProverTrace`, `RandomnessReplay`, and `ExactProtocolExecutionCapabilities` fixed | `ExecuteProtocol` is unchanged; a changed invocation witness must enter through the explicit Stage 4B bridge | Ambient provider behavior changes Core execution under fixed subject authority, invocation inputs, and execution capabilities |
| Randomness generator or entropy source | Swap the external generator while holding the same live `AdmittedProtocol` capability, its retained dependency/construction views, the exact invocation triple including `RandomnessReplay`, and `ExactProtocolExecutionCapabilities` fixed | Core execution reads only the replay and its authenticated distribution/joint-contract membership checks; probability fidelity remains a later nonclaim | Execution consults ambient entropy or treats a valid replay as proof of correct sampling probabilities |
| Algorithm implementation | Swap an unrelated codec, framing, sampler, or pure-function implementation while the exact admitted `CanonicalAlgorithmSpec`, dependency preimages/views, and identity-matched execution capabilities remain fixed | No normative operation reads the unrelated implementation; changing the selected execution capability changes a named input, while divergence under a fixed admitted contract is implementation nonconformance or `CheckerFailure`, not a silent semantic choice | Live implementation behavior selects semantics absent an identity-bearing contract and exact capability |
| Application policy | Change which otherwise valid statements an application accepts | Interface and Protocol facts remain fixed; the policy remains external | Policy restriction is smuggled into Interface admission |
| Artifact reader | Swap an unrelated ambient reader while holding the same admitted adapter capability, its retained authorized executable dependency, and exact `ExactRelationAdapterInterpreterExecutionCapabilities` fixed | No effect; changing or removing the authorized executable/checker capability changes a named input and requires adapter re-admission or yields `Refused`, while divergence under the admitted contract is nonconformance or `CheckerFailure` | A claimed adapter ID/preimage or unrelated binary is enough to select or authorize the result |
| Clock, filesystem, environment, or process identity | Vary all ambient process state | Pure identity/admission/check operations are invariant; an operational dependency must be named or cause refusal/failure | Ambient state changes a normative result |

This probe is a model closure result, not evidence that an implementation has
eliminated every ambient read. As a separate authority control, removing a
previously declared admitted adapter capability changes an explicit input and
returns `Refused`; it is not part of the fixed-input registry experiment.

### 10.2 Transport and regime orthogonality

| Variation | Expected result |
|---|---|
| Textual or binary transport changes but decodes to the identical canonical PIR graph | Same Protocol identity; local authentication/admission reruns |
| Alternative MLIR graph claims the same semantics but violates the one physical canonical form | Physical authentication negative before admission |
| Subject content fixed but semantic regime ID changes | Different semantic identity, or `Negative(RegimeMismatch)` for a root that still claims the old regime |
| Transport checksum/envelope changes while exact relation-artifact raw bytes remain equal | Same byte and observation identities after replay; transport checksum has no semantic role |
| Exact relation-artifact raw bytes change while the emitted semantic facts happen to remain equal | Different `RelationArtifactByteId` and observation ID; a later field comparison may still be affirmative |
| Package or archive layout changes while extracted semantic preimages remain exact | Subject IDs remain; package digest has no semantic authority |

### 10.3 Outcome separation witnesses

| Outcome | Exact witness |
|---|---|
| `Affirmative` | `L3` committed-object grounding with every exact input |
| `Negative` | `L2` public-port cardinality mismatch with retained witness and result-reference agreements; `C1` cross-pair composition mismatch with typed mismatch and unaffected-agreement facts but no resolved maps |
| `Unsupported` | Unknown artifact profile or certificate adjacency as composition |
| `CannotAnswer` | `F2` missing theorem/model basis or `O1` missing source evidence |
| `Refused` | `L2` binding bytes without a live admitted binding capability |
| `Malformed` | Truncated artifact framing or incomplete composition-spec structure |
| `CheckerFailure` | Artifact/correspondence checker terminates operationally before a semantic conclusion |

Changing only the witnessed condition moves to the corresponding result
constructor; no constructor is normalized into `Negative` or `false`.

### 10.4 Capability copy, reopen, mutation, FFI, and process probes

| Boundary | Subject capabilities | Checked-result capabilities |
|---|---|---|
| In-process handle copy | May alias only the same exact immutable authority and scope; it cannot widen subject, regime, role, or consumer | May alias only the exact result and retained input views |
| Raw carrier copy | Copies bytes and IDs only; owner authentication and admission rerun | Copies a replay record only; result checker reruns |
| Reopen | Starts from raw material and reruns all owning checks | Starts from record plus newly admitted inputs and rechecks |
| Mutation | Impossible through the immutable capability; a changed copy is a new candidate with recomputed identity | Invalidates the old record's exact-input match |
| Serialization | No live capability representation exists | Durable result is permitted only for a named consumer and remains non-authoritative until rechecked |
| FFI crossing | Authority resets; the receiving owner reruns physical authentication and domain admission before minting any attenuated local view | Raw result material crosses; newly admitted inputs and the exact result checker are required before local result authority |
| New process | Semantic IDs may be reconstructed; local capabilities never are | Every subject and relation is re-established as in `S1` |

These laws apply separately to every authenticated-candidate and
admitted-subject capability family for Protocol, Interface, Plan, transcript
construction, relation interface, relation instance, relation binding,
artifact profile, relation adapter, artifact observation, and composition
spec, as well as to every admitted attenuated/narrow view. Authentication of
one candidate family never supplies admission or another family's candidate
authority.
The checked-result column covers each exact completed-result type:
`CheckedPlanRealizes`, `CheckedArtifactInterfaceComparison`,
`CheckedCommittedObjectGrounding`,
`CheckedRelationCorrespondenceJudgment`,
`CheckedInstanceCorrespondenceJudgment`, `CheckedFSConstruction`, and
`CheckedCoreComposition`. Only an affirmative `CheckedCoreComposition` may
serve as later composition-context authority, and only an affirmative
`CheckedFSConstruction` may enter `FSCompile`; a negative checked result still
retains its exact question and facts but cannot authorize an affirmative-only
consumer.
For composition specifically, a negative result retains the exact admitted
child views, target attenuated view, regime, nonempty typed
`CoreCompositionComparisonFact` mismatch set, and unaffected agreements. It
retains no `ResolvedCoreCompositionMaps` and cannot inhabit
`CompositionContextAuthority`. A durable composition record for a named
consumer stores the bound IDs/regimes/checker identity/outcome and exactly one
of affirmative resolved maps or negative mismatch/agreement facts; reopening
re-admits the views and rechecks the selected outcome rather than deserializing
authority.

Special authority families have stricter probes:

- `CoreAdmissionWitness` is transaction-scoped. It cannot be copied outside
  the cold-admission transaction, reopened, mutated, serialized, passed across
  FFI, or reconstructed in another process. It is consumed only to close the
  enclosing Protocol admission and is then discarded.
- `ScopedCompositionFormationAuthority` is transaction-scoped and bound to
  one exact admitted composition spec, target `CoreAdmissionWitness`, target
  `CoreId`, and unforgeable invocation token. It carries no caller-selected map
  bundle. It cannot escape, be copied outside its formation transaction,
  reopen, serialize, cross FFI, or cross a process boundary. It is usable only
  inside a complete
  `FiatShamirFormationInput = {candidate,
  algorithm_dependency_preimages,
  dependency_authentication_capabilities,
  law_checker_capabilities,
  formation_authority}` to admit a matching `Composed` transcript construction
  during that target formation and is discarded when the transaction closes.
  No construction ID, dependency bundle, checked result, or serialized map can
  stand in for any field of that exact input.
- `PrivateWitnessAssignment`, each `SecretValueCapability`, and each
  invocation-local `RoleSecretInputValue` are
  occurrence-local confidential inputs or wrappers, not mandatory
  content-addressed subjects. The first two carry local secret authority;
  `RoleSecretInputValue` is only an explicit execution input wrapper and has no
  serialized form or authentication authority. In-process
  copying follows the secret owner's exact alias/scope contract; mutation
  produces a different local assignment. Reopen, serialization, FFI, or
  process transfer grants no witness authority under this model and must use a
  separately authorized confidential channel and local secret-owner checks.
  No public witness ID or equality claim is minted.
- Live dependency, adapter-executable, and checker capabilities are likewise
  process-local operational authority. Their semantic contract IDs, exact
  ABIs, and authenticated preimages may be reconstructed, but a receiving
  process or FFI owner must separately reacquire the authorized implementation
  and checker capability. Neither code bytes nor a contract ID grants it.

### 10.5 Laundering attempts

| Attempted laundering | Accepted input fact | Prohibited conclusion | Exact boundary response |
|---|---|---|---|
| Identity laundering | Correct semantic ID or digest | Live admission authority | `Refused` until owner admission succeeds |
| Capability laundering | Capability for one subject, role, view, or checked result | Authority for another subject or a widened parent view | Typed API refusal; the owner must mint the exact narrow capability from exact admitted inputs |
| Authentication laundering | Physically authenticated candidate | Whole-subject admissibility | Admission runs independently |
| Interface laundering | Admitted lossless Interface | Permission to restrict or change Protocol meaning | Interface admission rejects the changed candidate |
| Interface-to-invocation laundering | Decoded public-Statement subset and proof-message payload occurrences | Complete `CoreInvocationInputs`, `ProverTrace`, or `RandomnessReplay` | `CannotAnswer` until the Stage 4B bridge supplies and proves the exact invocation agreement |
| Plan laundering | Affirmative `CheckedPlanRealizes` | Completeness, cost, provider correctness, or proof success | Later question is `CannotAnswer` without its basis |
| Relation laundering | `CheckedArtifactInterfaceComparison`, `CheckedCommittedObjectGrounding`, or `CheckedRelationCorrespondenceJudgment` | Definition truth, instance truth, or witness satisfaction | `RelationSatisfies` remains separately owned |
| FS laundering | Unauthoritative `FSConstructionMaps`, or even affirmative `CheckedFSConstruction` without a theorem basis | `FSCompile` or any security-property transport | `CannotAnswer` without exact theorem/model/rule |
| Composed-FS formation laundering | A transcript-construction ID, dependency preimages, or prior checked-composition result without the exact live formation input | Admission of a `Composed` transcript construction during target formation | `Refused(missing exact candidate, dependency authentication, law checker, or transaction-scoped formation authority)` |
| Negative-composition laundering | Negative `CheckedCoreComposition` with exact mismatch and unaffected-agreement facts | `ResolvedCoreCompositionMaps` or `CompositionContextAuthority` | Typed refusal; only the affirmative payload variant retains maps and authorizes context |
| Composition laundering: graph union | Incomplete union offered as `CoreCompositionSpec` | Affirmative `CheckedCoreComposition` | `Malformed(missing complete origin and causal-edge partitions, interleaving, policies, combiner, and target fragment)` |
| Composition laundering: static link | Link proposal without an admitted spec and exact live child views | Affirmative `CheckedCoreComposition` | `Refused(missing composition-spec and child authority)` |
| Composition laundering: adjacency | Adjacent certificates offered as a composition relation | Affirmative `CheckedCoreComposition` | `Unsupported(not a CoreComposition relation)` |
| Composition laundering: target only | Independently admitted target but no spec, child maps, or relation inputs | Affirmative `CheckedCoreComposition` | `CannotAnswer(missing composition relation inputs)` |
| Property laundering | One property transport | Another property with different assumptions or loss | Separate exact request required |
| Randomness-replay laundering | Structurally and contract-valid deterministic replay | Proof that an external producer sampled with the declared probabilities | Later probabilistic/property analysis is required; execution establishes only the replayed occurrence result |
| Persistence laundering | Serialized admitted/result marker | Local capability | Re-authenticate, re-admit, and recheck |
| Target laundering | Admitted successor target | Correct predecessor/successor relation | Exact relation and maps still required |

### 10.6 Unknown-extension behavior

The following probes all fail closed:

- an unknown `pir.*` operation, attribute, observation class, event variant,
  challenge interpretation, or dependency kind fails canonical authentication
  or subject admission under the current regime;
- an unknown composition challenge/private-randomness/failure/reach-exit
  policy or child-reference kind fails spec authentication/admission rather
  than defaulting to independent behavior;
- an unknown Interface codec law or semantic default is unsupported or
  negative, never assumed lossless;
- an unknown relation artifact profile or correspondence field is
  `Unsupported`, not agreement; and
- an unknown invocation/replay record form, reference, ordinal, domain, or
  boundary is `Malformed` and mints no Core outcome rather than being skipped
  or resolved through an extension registry; and
- adding any of these meanings requires an explicit new semantic regime and
  therefore cannot preserve identity through carrier coincidence.

Diagnostic metadata and genuinely outer transport envelopes may evolve only
outside the canonical semantic graph and cannot be read by normative
consumers.

### 10.7 Opportunity probes

The design enables positive capabilities that are not mere repairs of current
failures:

1. **Independent semantic lenses.** One stable admitted Protocol can support
   several independently versioned lossless Interfaces, Prover Plans, relation
   bindings, and artifact observations. A researcher can compare the effects
   of packaging, prover construction, or relation interpretation without
   changing verifier-level Protocol identity or introducing a canonical bundle.
2. **Several transcript constructions over one Core.** Distinct exact
   transcript suites or application contexts produce separately identified FS
   Protocols and prefix maps over one stable interactive Core. Their structural
   comparison is possible without claiming either secure.
3. **Derivation comparison without identity pollution.** Different admitted
   composition specs may be compared even when they normalize to one intrinsic
   target Core, because checked provenance and child maps remain distinct from
   `CoreId`.
4. **Independent formal interpretation.** The language-independent closed
   Core algebra can be modeled without making a second production IR or
   treating MLIR implementation behavior as semantic authority.

The first opportunity is the required non-current capability probe; the others
show that the subject split creates a family of research operations rather
than only stricter refusals.

## 11. Candidate-level falsification summary

This section applies the same inputs, read-set, authority, outcome, replay, and
falsifier questions to Candidates A--E. A missing closure proof, normalizer, or
executable relation-specific simulation is counted as a conditional answer,
not excused as conceptual support; an explicit design-level schema is not
misreported as absent merely because no checker was executed. This is equal
scenario pressure; it does not select a candidate.

### 11.1 Equal-resolution operational comparison

| Candidate | Exact candidate input and normative read set | Authority and replay model | Outcome at this resolution | Decisive falsifier |
|---|---|---|---|---|
| A — rich quotient | Rich sealed representative plus exact projection regime; every normative consumer must read only the projected semantic object | Admission retains representative and projection basis; replay must rerun sealing, pre-erasure audit, projection, and consumer read-set closure | Gate-ineligible unless the fixed physical-canonical-carrier decision is reopened; individual semantic traces remain conditional | Two same-ID representatives yield different normative results, or projection erases a refusal-relevant distinction before checking it |
| B — canonical bundle | One canonical bundle plus exact named subobject ID; a consumer may read only that subobject and declared bundle closure | Every subobject must still receive owner admission and its own capability; replay authenticates the bundle and independently re-admits every consumed root | Gate-ineligible unless the fixed no-normative-bundle decision is reopened; afterward the semantic scenarios are expressible, but `I1`, `R1`, `L1`, and `S1` remain conditional on proving no bundle-authority transitivity | Adding an unrelated Interface/Plan changes another subobject's authority, or bundle admission substitutes for owner admission |
| C — typed satellites | Closed Core/Protocol graph plus exact independently identified satellites and narrow views | Owner-specific authentication/admission; local capabilities; relation results checked after independent target admission; full reset and replay across boundaries | All required model scenarios pass, including `R1` under the explicitly hypothetical partition observer | A bounded Protocol requires ambient meaning, the carrier is not bijective, or satellite dependencies form an authority cycle |
| D — typed event calculus | Exact `ProtocolProgramNF`, closed effect signature/imports/schedule, separately identified Interface/Plan/transcript/composition handler normal forms, first-class Relations subjects, and exact simulation question | Physical authentication and owner admission for the program and every dependent handler/subject; replay renormalizes exact preimages and reruns each relation-specific simulation | Complete design-level answers exist on all twelve axes; conditional on a fully enumerated finite syntax, total deterministic normalizer, decidable canonical equality, and executable Interface, `PlanRealizes`, artifact/correspondence, FS-map, and composition-map simulations | Normalization/equality is not total and decidable, an adequacy simulation needs ambient host behavior, a generic handled token substitutes for domain authority, or domain exceptions repeatedly reconstruct C inside the calculus |
| E — generative modules | Module, parameter assignment, elaborator contract, and closed elaborated C-style outputs; admitted consumers read only the closed outputs | Module/elaboration provenance is separate; outputs undergo ordinary C-style owner admission; replay may rerun elaboration but can always re-admit the closed result directly | Delegates semantic scenarios to C and therefore is not an independent admitted center; its own P1/elaboration termination and variance checks remain conditional | An admitted Protocol requires the module/elaborator to interpret it, elaboration is nonterminating/ambient, or generic constraints substitute for correspondence/property checks |

### 11.2 Same-family scenario matrix

Legend: `A` means the candidate gives an exact affirmative architecture answer;
`C` means the result depends on an additional exact discipline not instantiated
by that candidate; `F` means a fixed gate or required exact scenario fails;
`D->C` means the candidate delegates semantic authority to a closed Candidate-C-
style output rather than answering as a standalone center.

| Scenario family | A | B | C | D | E |
|---|---|---|---|---|---|
| `P1`--`P3`: quotient, regime, physical/admission split | `F` physical gate; quotient traces `C` | `F` bundle gate; member-level traces `A` if subobject physical form remains independent | `A` | `C` on exact normal form and pre-erasure audit | `D->C`; module normalization `C` |
| `I1`--`I2`: multiple Interfaces and semantic-change refusal | `C` on representative read sets | `A`, with bundle churn | `A` | `C` on exact handler preservation laws | `D->C` |
| `L1`--`L3`: artifact comparison, correspondence, grounding | `A` only after separate post-projection Relations objects | `A` if bundle authority stays nontransitive | `A` | `C`: first-class schemas exist; executable simulations remain | `D->C` |
| `R1`: Plan coverage and exclusive placement | `C` on rich-copy/read closure | `A` semantically; package churn remains | `A` under `Omega`; production owner deferred | `C`: exact Plan handler/simulation plus production observer remain | `D->C` |
| `F1`--`F2`: construction versus theorem/property | `C` on complete projected occurrence/prefix maps | `A` | `A` | `C` on exact transcript handler and prefix map | `D->C` |
| `C1`--`C2`: repeated children, terminals, full composition | `C`: link/reseal must grow full policies/maps | `A` if bundle construction keeps target admission independent | `A` | `C`: exact operator/policies exist; normalizer and map simulation remain | `D->C`; module elaboration audit `C` |
| `T1`: structural result without property transport | `A` under typed result separation | `A` | `A` | `C` on handler-result type separation | `D->C` |
| `S1`: serialization and capability reset | `C` on projection/read-set replay | `C` on preventing bundle transitivity | `A` | `C` on explicit local capability semantics | `D->C`; provenance replay separate |
| `O1`: local OIR validity without source coverage | `A` if consumers use projected source views | `A` if source root is named, not inferred from package | `A` | `C` on handler adequacy boundaries | `D->C` |
| Positive opportunity | Rich diagnostics and one workbench/carrier | Deterministic archival snapshot | Independent lenses, constructions, derivations, and models | Mechanized effect semantics | Reusable protocol-family authoring |

Candidate A's fixed-gate ineligibility is separate from its intrinsic
falsifier. Candidate B's no-normative-bundle gate is likewise separate from
its intrinsic falsifier; it remains a fully analyzed reopening alternative
whose main risk is authority/product coupling, not an observed semantic
impossibility. Candidate D is an explicit alternate semantic center with
complete design-level axis schemas; its conditional disposition is caused by
the still-unclosed finite syntax, normalization/equality, and executable
simulation obligations, not by missing Relations, Plan, outcome, or
composition schemas. Candidate E receives a delegation verdict: it is
evaluated as an authoring overlay whose closed outputs carry semantic
authority, not as a second admitted center. No row is used as a convergence
selection.

## 12. Residual obligations and exit interpretation

The scenario suite closes the Stage 3 semantic-model gate with these bounded
residual obligations:

- Stage 4B must instantiate the Plan-field read-set and classification checker
  against exact OIR semantics; until then concrete classification questions
  are `CannotAnswer`.
- Stage 4A/Analysis must own exact `FSCompile`, property transport,
  equivalence/refinement, and property-composition judgments; no affirmative
  result is preloaded here.
- Stage 4 endpoint work must define `LocalOirValid`, OIR identity, and
  `ProjectionCorrect`; the source-free split in `O1` is the required handoff.
- Implementations must separately demonstrate physical canonicality,
  no-ambient-read behavior, replay reset, and correspondence with this model.
- Durable checked-result schemas must be introduced only for named independent
  consumers and must bind every input, regime, checker, outcome, and residual
  trust named in `S1`.

These are owner handoffs and implementation obligations, not failures of the
Stage 3 subject architecture. Reopening any forbidden collapse, weakening an
outcome class, or omitting a decisive falsifier invalidates this validation
record.
