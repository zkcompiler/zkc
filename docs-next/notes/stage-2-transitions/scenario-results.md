# Stage 2 scenario and adversarial pressure-test results

> **Document kind:** Temporary architecture research note
> **Document state:** Independent pressure-test pass; convergence input, not a
> decision
> **Authority:** None. This note does not define a transition, select a public
> API or wire format, ratify a checker, or authorize implementation work.
> **Scope:** The four candidate transition families, disciplined hybrids, the
> complete Stage 2 scenario portfolio, cross-candidate falsifiers, and newly
> enabled design opportunities.
> **Method:** Static inspection of the selected Stage 1 architecture, current
> normative specifications, implementation entry points, tests as bounded
> correspondence evidence, and the Stage 2 internal and external research
> dossiers. No test was executed for this pressure-test pass.
> **Disposition:** Use this note as an independent input to Stage 2
> convergence. Promote only reviewed conclusions into their exact durable
> owners, record reversal triggers, then delete this page.

## 1. Claim discipline

This note uses four explicit labels:

- **Observed** means the behavior or boundary is stated in a current
  specification or visible in the inspected implementation. It remains a
  statement about the current system, not the selected target.
- **Inferred** means several observations or external mechanisms support a
  design consequence. It is not implementation evidence or a normative rule.
- **Preferred hypothesis** means the pressure test currently favors one
  candidate or disciplined combination. It is a recommendation to the Stage 2
  convergence pass, not a ratified architecture.
- **Deferred** means the evidence is insufficient or the exact semantics belong
  to a later owner. Deferral must retain an owner and a falsifier.

The candidates are evaluated in their strongest coherent forms. Candidate B
is split into an in-process algebra (`B-local`) and a portable universal
artifact (`B-wire`), because the portable form creates a compatibility product
and obtains benefits that the local form does not. Candidate D is allowed its
declared direct-recomputation and trusted-effectful degeneracies; it is not
artificially failed merely because every edge does not admit a compact witness.

## 2. Executive result

**Observed.** The current system already uses different authority shapes at
different boundaries:

- decoding and admission return different opaque types;
- admission retains process-local immutable authority and serialization ends
  its continuity;
- relation correspondence and property derivation produce judgments rather
  than new Protocol authority;
- compiler construction, successor re-admission, and decision recomputation
  are distinct steps;
- paired PIR/OIR storage retains source-relative projection authority in one
  process, while standalone OIR admission establishes only local validity; and
- verifier rejection, supplier refusal, and execution failure already occupy
  different result paths.

No inspected current consumer requires one portable record that represents all
of these transitions. No common mathematical composition law was found across
admission, derivation, correspondence, projection, effectful execution,
appraisal, and reliance.

**Inferred.** The four candidates are not mutually exclusive at the mechanism
level, but none is a good whole-system center by itself:

1. Candidate A best preserves domain and bridge ownership across heterogeneous
   relations. It needs an enforceable shared review/catalog discipline or it
   risks semantic drift and poor global inspection.
2. Candidate B provides the strongest generic graph and replay tooling, but
   `B-local` still delegates every meaningful check to domain owners, while
   `B-wire` creates a universal schema, identity, retention, and evolution
   promise without a demonstrated v0 consumer. Its generic composition reduces
   to relation-specific registered laws, and effectful or policy-qualified
   edges require a separate fragment.
3. Candidate C is the strongest model for the canonical Protocol lifecycle and
   process-local least authority. It does not replace mathematical judgments,
   durable independent derivations, or effect semantics.
4. Candidate D is strongest for expensive search, synthesis, compilation,
   projection, or realization when a materially smaller stable validator
   exists. Making it universal would add artificial producer/witness layers to
   cheap deterministic checks and misdescribe operational occurrences as pure
   validated arrows.

**Preferred hypothesis.** Use a disciplined hybrid with:

```text
Candidate A as the ownership and contract baseline
  + Candidate C for lifecycle and process-local authority
  + Candidate D selectively for proposal-heavy, independently checkable edges
  + no universal TransitionId or portable transition artifact by default
```

The shared project layer should own a descriptive contract schema, a typed
subject-reference vocabulary, catalog completeness checks, and global
non-collapse rules. It should not own relation truth, generic semantic
composition, capability continuity, or a universal serialized result.

This hypothesis survives every scenario below without changing the fixed Stage
1 subject model. It remains falsifiable by a concrete universal consumer, by
failure to keep domain contracts coherent without a central executable
algebra, by widespread inability to build smaller validators, or by
cross-process consumers that cannot economically reconstruct authority.

## 3. Evidence base

### 3.1 Current observations

| Observation | Inspected evidence | Limit of the observation |
|---|---|---|
| Decode and admission are separate authority states | [`Artifact.h`](../../../include/zkc/Artifact/Artifact.h) and [`Artifact.cpp`](../../../lib/Artifact/Artifact.cpp) distinguish `DecodedPirArtifact` from `AdmittedPirArtifact`; admission re-runs `SealEngine::recheck` | The current subjects and retained environment are not the final Stage 1 closure |
| Capabilities are opaque, copyable only over immutable private storage, and not serialized | [`Artifact.h`](../../../include/zkc/Artifact/Artifact.h) exposes IDs and the admitted environment but no mutable IR accessor | C++ type opacity does not itself define future FFI, thread, delegation, or revocation semantics |
| Current admitted authority retains more than the cited identity closure | [`ProtocolEnvironment.h`](../../../include/zkc/Registry/ProtocolEnvironment.h) contains the complete vocabulary/profile provider and admitted artifacts retain it | This is evidence for explicit consumer read sets, not proof that the target must retain a broad environment |
| Static link produces an unauthoritative new Open PIR | [`boundaries.md`](../../../docs/spec/boundaries.md) and [`LinkEngine.h`](../../../include/zkc/Semantics/LinkEngine.h) require the result to cross seal again | Current link is not yet the Stage 1 semantic Core-composition model |
| Projection is source-relative in process | [`Projection.h`](../../../include/zkc/Dialect/Pir/Transforms/Projection.h) and [`PirProject.cpp`](../../../lib/Dialect/Pir/Transforms/PirProject.cpp) retain the source backing and check exact source-position coverage | The current API lacks explicit `ProtocolInterfaceId` and `ProverPlanId` inputs |
| Standalone OIR admission is target-local | [`PirProject.cpp`](../../../lib/Dialect/Pir/Transforms/PirProject.cpp) rechecks OIR identity and locally cited contracts without a source obligation set | It cannot establish omitted-source absence or projection coverage |
| Current compiler checking authenticates concrete successors and recomputes decisions | [`PirCompilerProvider.cpp`](../../../lib/Compiler/PirCompilerProvider.cpp) replays the transform and re-admits the successor; [`CompilerCore.cpp`](../../../lib/Compiler/CompilerCore.cpp) recomputes the exact selected ordinal | Producer and checker share implementations and environment; this is not an independent validator or portable certificate |
| Analysis already separates authenticated projection from rule-owned derivation | [`soundness.md`](../../../docs/spec/soundness.md) and the PIR soundness adapter separate artifact facts, explicit plans, derivations, and conditional judgments | Current artifact-qualified subjects and current FS rule are not the selected two-Protocol `FSCompile` relation |
| Relation correspondence is post-seal and can report disagreement without invalidating the Protocol | [`relations.md`](../../../docs/spec/relations.md) separates contract admission, computed/cross-checked/asserted facts, and what is never established | Current wiring can read labels that Stage 1 moves into an exact Protocol Interface |
| Generalized deployment, evidence appraisal, and reliance are not implemented semantic authorities | The current [status](../../../docs/status.md) and endpoint reconstruction distinguish implemented OIR/interpreter/emission slices from future generalized boundaries | Later target contracts must not be presented as current implementation facts |

These observations support mechanism selection and identify hidden-input
pressures. They do not establish that the preferred hypothesis has been
implemented or proven correct.

The completed [current transition catalog](current-transition-catalog.md)
also records four present documentation/correspondence tensions: relation
disagreement is specified as refusal but implemented as a negative report;
the emitter's effective deterministic-input set is wider than one documented
tuple; the normative attributable-run record is wider than current public
executor results; and the normative overview omits the separately canonical
Relations owner. This pressure test does not adjudicate those current
contracts. It uses them to require explicit outcome, read-set, record-strength,
and ownership decisions in the target rather than silently inheriting either
side.

### 3.2 External constraints used narrowly

The [external-case dossier](cases/transition-and-checking-models.md) supplies
four high-value constraints:

1. CompCert and Alive2 show that preservation or refinement is meaningful only
   over exact source/target semantics, observers, domains, and checker limits;
   they do not imply one relation for all zkc edges.
2. Proof-carrying code and LRAT show when an untrusted producer plus a smaller
   checker and durable witness can reduce a trust boundary; they do not imply
   that every zkc relation has a compact certificate.
3. MLIR dialect conversion establishes configured structural legality, not
   Protocol admission or semantic preservation.
4. capability systems and provenance/attestation architectures reinforce that
   live authority, persistent content, semantic checking, appraisal, and
   consumer reliance are distinct.

**Inferred.** A common field envelope can improve review and tooling, but no
external case makes the envelope the authority for its payload's truth. A
certificate is justified by one claim and one consumer, not by the existence
of a transition diagram.

## 4. Candidate fitness before scenario details

The table records architectural fit, not implementation status:

- `strong` means the candidate's center expresses the pressure directly;
- `conditional` means it survives only through an explicit edge-specific
  mechanism, subvariant, or loss of a headline benefit; and
- `poor` means the currently proposed center conflicts with the pressure or
  creates a product commitment with no demonstrated benefit.

| Pressure | A: domain contracts | B-local: common algebra | B-wire: common artifact | C: capability lifecycle | D: proposal/validation | Preferred hybrid |
|---|---|---|---|---|---|---|
| Heterogeneous semantic relations | Strong | Conditional: indexed dispatch owns no semantics | Conditional: opaque or frequently evolving payloads | Strong outside the lifecycle | Conditional: direct-check degeneracy required | Strong |
| Process-local admission authority | Conditional: depends on concrete APIs | Conditional: algebra must not mint portable authority | Conditional: the artifact remains capability-neutral and the receiver re-admits | Strong | Conditional: checked result must still mint a local capability | Strong |
| Cheap deterministic admission or analysis | Strong | Conditional: central wrapper adds little | Poor absent an independent reader | Strong | Conditional: producer/witness split is unnecessary | Strong |
| Expensive heuristic transform or projection | Conditional: must define a validator strategy | Conditional: still needs an edge checker | Conditional: useful only if a portable consumer exists | Conditional: capability alone does not reduce producer trust | Strong when checker is smaller | Strong |
| Cross-process independent checking | Conditional per edge | Conditional without a wire form | Strong mechanically, not semantically | Conditional: recheck from subjects or add an exception | Strong for justified certificates | Strong selectively |
| Effectful deployment or invocation | Strong with domain effect contracts | Conditional: needs a separate event/effect fragment | Conditional: needs an effect/occurrence payload and cannot promise replay | Conditional: gates authority but does not model observations | Conditional: preflight/receipt is not execution replay | Strong with domain effect contracts and capabilities |
| Evidence, appraisal, and reliance | Strong | Conditional: must prevent authority cycles | Conditional: must keep evidence, assessment, and reliance as separate typed records | Conditional: can gate local use only | Conditional: semantic certificate is only an appraisal input | Strong |
| Mathematical composition | Conditional on explicit domain laws | Conditional: generic composition exists only after law registration | Conditional with a large compatibility surface | Conditional: capability chaining is procedural only | Conditional: certificate chaining proves at most named conjunction | Conditional on exact relation laws |
| Generic catalog and provenance tooling | Conditional: requires projections and lints | Strong | Strong | Conditional: opaque handles need safe views | Conditional: validator registry helps only selected edges | Strong if tooling reads a semantics-neutral catalog |
| v0 wire and evolution risk | Strong by default | Strong if kept local | Poor without a consumer and compatibility window | Strong by default | Strong when certificates are demand-driven | Strong |

**Preferred hypothesis.** Candidate B's useful v0 contribution is not a
universal transition object. It is the narrower idea that exact subject
references, declared dependency closures, relation names, outcomes, and
checker regimes should be inspectable through a common catalog projection.
That projection may become machine-readable and lintable without becoming a
runtime semantic algebra or wire-level authority.

## 5. Scenario portfolio

The portfolio combines the Stage 2 charter, candidate framework, lifecycle,
semantic-bridge, and endpoint workstreams. A scenario passes only if it
preserves the required claim strength and category distinctions; merely
returning an error is insufficient.

### 5.1 Lifecycle, identity, and closure scenarios

| ID | Scenario and perturbation | Required result | Decisive pressure |
|---|---|---|---|
| `L1` | Two authoring histories differ only in labels, redundant defaults, and observer-irrelevant order | One physical canonical graph and one semantic identity; proposal provenance may differ | Target identity must exclude search history while authentication rejects noncanonical representatives |
| `L2` | Persist an admitted Protocol and load it in a fresh process | Decode reconstructs content; authentication and admission mint new local authority | Any serialized `admitted` marker is unauthoritative |
| `L3` | Add one uncited resolver entry, then separately change one cited preimage | Uncited addition has no effect; cited change refuses or produces a deliberately new subject | Declared closure must be extensional, not merely logged |
| `L4` | Copy an admitted handle, reopen a mutable branch, perform no edit in one branch and a semantic edit in another | In-process handle copy may preserve source authority; both branches are raw; no-op may recover the ID only after rechecking; real change mints a new ID | Capability continuity follows controlled construction, not content coincidence |
| `L5` | Keep semantic subject fixed while changing transport, then keep bytes fixed while changing semantic regime | Transport may vary after exact representation authentication; regime change cannot silently preserve semantic identity | Byte, carrier-schema, semantic-regime, and subject identities remain separate |
| `L6` | Attempt persistence of a canonical but unadmitted candidate | The transport makes its unauthoritative grade unmistakable: either the official admitted artifact refuses or a distinctly typed candidate/cache envelope is used | Prevent persistence from laundering a candidate into deployable authority |

### 5.2 Dependent-subject and semantic-bridge scenarios

| ID | Scenario and perturbation | Required result | Decisive pressure |
|---|---|---|---|
| `S1` | One Protocol has two external Interfaces with different names or packaging | Protocol-only judgments are reusable; interface-sensitive correspondence and OIR consume the exact `ProtocolInterfaceId` | Bare `ProtocolId` cannot launder an external mapping |
| `S2` | One Protocol has two ProverPlans and supplier strategies | Verifier-visible judgments remain Protocol-level; plan-sensitive coverage, cost, completeness, projection, or realization cites `ProverPlanId` exactly | Plan state cannot arrive through compiler or realization ambient state |
| `S3` | Admit a relation interface before relation bytes arrive, then interpret later bytes | Later interpretation can add computed or cross-checked observations without changing Protocol identity or proving relation truth | Relation subject admission and artifact interpretation have different authority |
| `S4` | A well-formed relation artifact disagrees on one field while other facts agree | Artifact interpretation records a successful negative `RelationArtifactObservation`; a subsequent exact correspondence check may return a negative judgment that retains affirmative subfacts and residual obligations | A negative observation or judgment is not malformed input, unsupportedness, or refusal, and the two result categories remain distinct |
| `S5` | A complete decidable property query evaluates to false; a second query is unsupported; a third search is inconclusive | Three different outcomes: successful negative, unsupported, and inconclusive/cannot-answer | A flat success/error or validity Boolean fails |
| `S6` | Construct an FS Protocol from a fresh-coin Protocol, then remove the theorem/model basis; also request two property tracks with different assumptions | The FS Protocol remains an admitted subject; `FSCompile` is unavailable; each property transport remains separately qualified | Construction, two-Protocol relation, and property transport must not collapse |
| `S7` | A compiler searches many candidates, proposes a cheaper successor, and omits one member of the claimed comparison domain | The successor is separately admitted; the named relation is validated; optimum is refused unless domain completeness is checked | Target identity, transform correctness, property transport, and selection optimality are four claims |
| `S8` | An identity/no-op plan and an intentional content-changing plan run on the same predecessor | The identity result reproduces the predecessor subject; the changing result mints a successor and cites an exact relation | A new ID proves neither equivalence nor intentional correctness |
| `S9` | A valid Protocol contains an endpoint obligation unsupported by one target | Typed projection refusal; source admission remains intact and no partial source-coverage capability is minted | Unsupported target capability is not source invalidity |
| `S10` | A locally valid OIR is supplied without its source or source-bound projection evidence | Local OIR admission may succeed; source-relative coverage is unknown or refused | A target cannot prove absence of omitted source facts |
| `S11` | Compose two children, including two occurrences of the same child, with an explicit causal seam and interleaving | Construct and admit one new Core with tagged occurrences, schedule, challenge, failure, and dependency closure | Protocol composition is not transition or certificate chaining |

### 5.3 Endpoint, operational, and reliance scenarios

| ID | Scenario and perturbation | Required result | Decisive pressure |
|---|---|---|---|
| `E1` | Bind one OIR to two exact supplier/target configurations | Two binding subjects or capabilities as required; OIR meaning remains unchanged; provider designation does not prove provider correctness | Configuration identity and live provider authority are separate |
| `E2` | A complex emitter produces deterministic bytes, and a second consumer wants a preservation claim | Production observation is not `RealizesOir`; use a smaller target-specific validator if one exists, otherwise state a trusted producer or bounded evidence grade | Determinism and packaged IDs do not prove correspondence |
| `E3` | Execute a verifier that rejects a proof; separately fail before execution because a supplier is unavailable | Verifier `Reject` is a completed semantic result; supplier failure is refusal or operational failure | Endpoint result and transition execution status require orthogonal axes |
| `E4` | A prover produces proof bytes; no verifier run is available | Report produced bytes and observations only | Prover success does not imply verifier acceptance, completeness, witness truth, soundness, or zero knowledge |
| `E5` | Deployment or invocation emits one externally visible action and then fails | Report the last protected event, remaining effects, cleanup/retry boundary, and a partial-effect failure | Pure transition algebra and rollback assumptions are invalid here |
| `E6` | One observation is recorded, appraised under one policy, accepted by one consumer, and rejected by another | Preserve observation, evidence record, assessment, and both use-specific reliance decisions | Neither appraisal nor reliance changes Protocol, OIR, realization, or run meaning |
| `E7` | An older consumer sees a new meaning-bearing relation, evidence predicate, or certificate payload | Fail closed for the unknown semantic kind while retaining explicitly safe transport/provenance handling | Opaque extension bytes cannot count as a checked edge |
| `E8` | A durable receipt is present but one cited declaration preimage is missing | Authenticity may still be reported; semantic checking is cannot-answer/refused, and no local authority is minted | A digest or signature does not supply the semantic closure it names |
| `E9` | One admitted realization is activated under two deployment topologies or resource snapshots | Realization identity remains fixed; deployment binding, live instance, occurrence, observations, and reliance context differ | Physical placement and live authority cannot remint endpoint semantics |

### 5.4 Cross-framework fitness matrix

Legend:

- `direct` means the candidate's architectural center handles the scenario;
- `qualified` means it survives only with an explicit domain-specific
  mechanism or loses a claimed uniformity benefit; and
- `adverse` means the scenario directly pressures the candidate's proposed
  center at v0.

| Scenario | A | B-local | B-wire | C | D | Preferred hybrid | Principal result |
|---|---|---|---|---|---|---|---|
| `L1` equivalent histories | Direct | Direct | Qualified | Direct | Direct | Direct | Domain identity must ignore proposal history |
| `L2` cross-process admission | Direct | Qualified | Qualified: record remains capability-neutral | Direct | Qualified | Direct | Re-admission is mandatory |
| `L3` resolver substitution | Qualified: needs lint/check discipline | Direct only if closure is enforced, not logged | Qualified | Direct if capability captures the minimal closure | Direct if validator reads exact closure | Direct | Uncited changes must be observationally irrelevant |
| `L4` copy/reopen/change | Qualified | Qualified | Qualified: artifact records no live authority | Direct | Qualified | Direct | Local authority and semantic identity diverge |
| `L5` regime/transport evolution | Direct | Qualified | Qualified, with central compatibility coupling | Direct | Direct per certificate regime | Direct | Compatibility claims remain typed and local |
| `L6` unadmitted persistence | Direct through distinct artifact grades | Qualified | Qualified: proposal and checked grades require distinct typed states | Direct | Qualified | Direct | Official subject artifact and proposal cache differ |
| `S1` two Interfaces | Direct | Qualified | Qualified | Direct | Direct | Direct | Interface identity closes every sensitive bridge |
| `S2` two Plans | Direct | Qualified | Qualified | Direct | Direct | Direct | Plan placement is an explicit transition input |
| `S3` later relation bytes | Direct | Qualified | Qualified | Direct outside lifecycle | Direct if interpretation needs validation | Direct | Admission and interpretation are separate |
| `S4` negative correspondence | Direct | Qualified outcome index required | Qualified outcome and subfact schema required | Direct outside lifecycle | Direct | Direct | Negative is a checked result |
| `S5` negative/unsupported/inconclusive analysis | Direct | Qualified product outcome required | Qualified and schema-heavy | Direct outside lifecycle | Qualified: direct-check degeneracy required | Direct | One Boolean cannot represent the result |
| `S6` FS construction/theorem/transport | Direct | Qualified by three relation kinds | Qualified with high schema churn | Direct outside lifecycle | Direct for theorem checks, not construction | Direct | No global `FS-valid` state |
| `S7` search and optimum | Qualified | Qualified | Qualified if an independent reader exists | Qualified | Direct | Direct | Per-result relation and domain completeness differ |
| `S8` identity/change transform | Direct | Qualified | Qualified | Direct for successor authority | Direct | Direct | Identity effect is declared, not inferred |
| `S9` unsupported projection | Direct | Qualified | Qualified | Direct for authority gating | Direct if checker is smaller | Direct | Refusal does not invalidate source |
| `S10` source-free OIR | Direct | Qualified | Qualified: record cannot synthesize omitted source closure | Direct | Direct if certificate binds source closure | Direct | Local validity is weaker than correspondence |
| `S11` semantic composition | Qualified by a Protocol-owned constructor | Qualified: the algebra supplies no generic law or Core constructor | Qualified, with a larger false-composition surface | Qualified | Qualified | Direct only through a separate Stage 3 constructor | New Core construction is not edge chaining |
| `E1` supplier alternatives | Direct | Qualified | Qualified | Direct for local provider authority | Qualified | Direct | Binding/configuration is not provider truth |
| `E2` realization checking | Qualified | Qualified | Qualified if a real consumer exists | Qualified | Direct when validator is smaller | Direct | Trusted producer remains an honest fallback |
| `E3` reject versus failure | Direct | Qualified effect/result product required | Qualified and schema-heavy | Qualified | Qualified | Direct | Semantic result and operational status are orthogonal |
| `E4` prover output only | Direct | Qualified | Qualified | Qualified | Qualified | Direct | Observation strength cannot be inflated |
| `E5` partial effect | Direct with effect contract | Qualified through a separate effect/event fragment | Qualified and schema-heavy | Qualified: capability gates but does not describe effects | Qualified: requires its effectful degeneracy | Direct | Effects require occurrence and retry semantics |
| `E6` evidence/appraisal/reliance | Direct | Qualified | Qualified: requires separate record and policy kinds | Qualified | Qualified | Direct | Relying policy remains consumer-owned |
| `E7` future semantic kind | Direct, fail closed locally | Qualified by central registry evolution | Adverse to universal compatibility surface | Direct | Direct per edge | Direct | Extension must not silently weaken checking |
| `E8` missing preimage | Direct | Qualified | Qualified | Direct | Direct | Direct | Authentication does not imply semantic availability |
| `E9` two deployments | Direct | Qualified effect/occurrence fragment | Qualified and schema-heavy | Direct for scoped live authority | Qualified: validation is not the organizing mechanism | Direct | Content, configuration, and occurrence identities differ |

The matrix does not give the hybrid automatic authority. It shows only that
its mechanism-selection rule avoids forcing all rows through one abstraction.
Each concrete edge still needs its own contract, checker basis, and owner.

## 6. Cross-candidate falsification results

### 6.1 Hidden-read substitution

**Probe.** Hold every declared input fixed while changing an uncited resolver,
interface, plan, compiler, supplier, theorem, or policy entry.

**Required behavior.** No normative result changes. If it does, the alleged
contract is not closed and the hidden value becomes an exact input.

**Candidate pressure.** A is at risk when its shared schema is editorial only.
B is at risk if a universal artifact records claimed dependencies but does not
make relation-specific checkers consume only them. C is at risk when an opaque
capability captures a broad mutable environment. D is at risk when the
validator shares hidden producer state.

**Result.** No candidate gets closure from metadata alone. The preferred
hypothesis therefore requires extensional closure checks: changing anything
outside the declared read closure cannot change the normative result.

### 6.2 Identity laundering

**Probe.** Substitute a different Interface, Plan, semantic regime, checker
regime, target, or supplier binding behind the same `ProtocolId`.

**Required behavior.** Interface-, plan-, target-, or checker-sensitive results
refuse or produce separately identified outputs. Protocol-only questions may
remain reusable.

**Result.** Candidate C prevents many accidental calls through capability
types, but only A's explicit domain contracts or D's exact validators state the
mathematical consequence. A central B reference type is useful for routing but
cannot decide substitutability generically.

### 6.3 Capability laundering

**Probe.** Serialize, print, cross an FFI boundary, reopen, or mutate a value
that claims admission or checked-pair authority.

**Required behavior.** The receiving side obtains bytes, references, or an
unauthoritative proposal and must re-authenticate and re-admit or recheck.

**Result.** Candidate C is the clear lifecycle mechanism. B-wire is rejected as
a portable authority carrier; at most it can carry a capability-neutral claim
that a new process independently checks. D's certificate also cannot preserve
the original capability.

### 6.4 Relation inflation

**Probe.** Ask a structural admission, local OIR check, transform validator,
signed receipt, or successful execution for a stronger conclusion such as
soundness, full source coverage, completeness, or reliance authorization.

**Required behavior.** Return only the named relation or refuse the stronger
question.

**Result.** Domain/bridge ownership is a hard constraint. A universal result
kind named `validated` or `certified` fails even if its payload includes a
relation tag, unless the relying API exposes the exact claim and non-claims.

### 6.5 Composition laundering

**Probe.** Chain individually valid relations whose assumptions, direction,
observer sets, quantitative losses, policies, or semantic regimes differ.

**Required behavior.** The chain is only procedural provenance or a
conjunction until an exact owner supplies a composition law and checks all
transported conditions.

**Result.** Candidate B does not obtain generic semantic composition from a
typed arrow graph; its strongest safe `compose` operation is parameterized by
an edge-specific theorem. Candidate D certificates likewise do not compose by
ID adjacency. Candidate C's capability chaining is only operational
eligibility. A and the preferred hybrid make the lack of a law explicit.

### 6.6 Negative-result confusion

**Probe.** Compare a derived false property, negative correspondence,
unsupported feature, missing theorem, incomplete checker, malformed input, and
operational failure.

**Required behavior.** Preserve distinct execution, input, check, judgment,
and authority dimensions.

**Result.** A common diagnostic envelope is acceptable; one flat status enum
is not. Domain owners must define the valid cross-product and prevent
impossible combinations. This argues for shared outcome dimensions in the
catalog, not one universal runtime `Result` type.

### 6.7 Effect erasure

**Probe.** Fail after publication, resource allocation, service invocation, or
another externally visible action.

**Required behavior.** Report partial effects, last protected event,
idempotence, retry identity, cleanup, and residual authority. Never report a
pure refusal with implied rollback.

**Result.** A domain-owned effect/occurrence model is mandatory for
realization, deployment, and invocation. B and D survive only by admitting a
separate effectful fragment, which substantially narrows their claim to be a
universal transition center.

### 6.8 Authority cycle

**Probe.** Feed a producer assertion, provenance record, observation,
certificate signature, appraisal, or reliance decision backward as authority
to define or admit a Protocol, Interface, relation, OIR, or realization.

**Required behavior.** Reject the cycle. Later records may cite earlier
subjects; they cannot redefine them.

**Result.** Source owner, bridge owner, target owner, and relying consumer must
remain independently named. A shared graph may display their edges but may not
turn reachability into truth.

### 6.9 Wire without a consumer

**Probe.** Require every proposed durable transition object to name its
independent producer and consumer, retention window, release relationship,
checker availability, compatibility promise, and cheaper alternative.

**Required behavior.** No universal or edge-specific wire object is introduced
without a positive answer.

**Result.** `B-wire` currently fails this probe as the global v0 center. D
passes only selectively. The preferred hypothesis keeps local capabilities and
direct recomputation as first-class final choices, not temporary omissions.

### 6.10 Diagnostic collapse and unknown kinds

**Probe.** Force an identity mismatch, uncovered obligation, illegal rewrite,
unavailable supplier, unrecognized relation kind, and unknown evidence
predicate.

**Required behavior.** Preserve the owning domain's semantic distinctions and
fail closed for unknown meaning-bearing kinds. Generic tooling may retain safe
transport metadata without recognizing semantic authority.

**Result.** Candidate A requires a catalog adapter discipline; Candidate B
requires extension points that do not degrade into opaque trusted payloads;
Candidate C must expose safe diagnostic views; Candidate D must avoid one
uninformative certificate-verification error.

### 6.11 Validator duplication

**Probe.** Compare producer and validator implementations, dependency closure,
semantic model, algorithmic complexity, and release cadence.

**Required behavior.** Select D only when the validator is materially smaller,
more stable, independently specified, or independently implemented enough to
justify the boundary. Otherwise use direct recomputation or name the trusted
producer honestly.

**Result.** Current compiler replay is a valuable checked boundary but does not
yet satisfy the independence hypothesis. This does not weaken its current
claim; it prevents Stage 2 from overstating the future architecture.

### 6.12 Shared-mechanism extraction

**Probe.** Propose one common runtime type or checker protocol for two edges.
Require identical semantic relation shape, authority lifetime, outcome
structure, replay need, effect class, and consumer—not merely similar fields.

**Required behavior.** Extract only the genuinely shared mechanism. Keep
relation payloads, capability minting, effect handling, and reliance local when
any of those axes differ.

**Result.** The current evidence justifies a shared descriptive schema and
subject-reference vocabulary. It does not yet justify a universal executable
transition algebra or artifact.

## 7. Newly enabled opportunities

The pressure test must remain generative. The following opportunities are not
repairs for failed boundaries; they become possible once subject, relation,
authority, and persistence are separated.

### 7.1 Multiple producers behind one stable acceptance boundary

An optimizer, importer, normalizer, projector, or emitter can evolve
independently—or several implementations can compete—when every candidate is
checked against the same exact edge contract. Search heuristics, seeds, traces,
and internal MLIR pipelines remain provenance unless they alter the admitted
result.

**Enabling mechanism:** selective Candidate D over Candidate A-owned relation
contracts.

**Promotion condition:** the validator must be smaller or more stable than the
producer and closed over exact source, target, regime, configuration, and
observer inputs.

### 7.2 Remote checking without portable admission authority

A remote worker may return a candidate subject, source-bound witness, or
edge-specific certificate. The receiving process checks it and mints its own
capability. This permits distributed search and caching without serializing an
`AdmittedProtocol` or treating the worker as the semantic authority.

**Enabling mechanism:** C's serialization degradation plus D's optional
edge-specific evidence.

**Promotion condition:** identify the exact remote consumer, available
dependency preimages, privacy constraints, replay cost, and certificate
compatibility window.

### 7.3 Safe reuse across Interfaces and Plans

Protocol-level Analysis can be cached by exact Protocol subject while
Interface correspondence, plan-sensitive completeness, projection, cost, and
realization remain dependent results. Several external APIs and prover
strategies can share one Core without making ABI labels or private algorithms
Protocol identity.

**Enabling mechanism:** fixed Stage 1 identities plus A-owned dependent bridge
contracts and C-owned admitted inputs.

**Promotion condition:** Stage 3 must define the exact exported Protocol facts
and the complete Interface and Plan read sets.

### 7.4 Assurance escalation per edge

One relation can evolve from trusted production, to deterministic replay, to
translation validation, to proof-producing checking without changing every
other transition. The semantic claim remains stable while the checking and
evidence grade strengthens.

**Enabling mechanism:** separate relation, checker regime, capability, and
durable evidence identity.

**Promotion condition:** the stronger checker must establish the same named
relation and state all changed assumptions, bounds, and unsupported cases.

### 7.5 Queryable provenance without a universal fact root

Domain-owned subjects, judgments, observations, and certificates can expose a
common capability-neutral metadata projection for visualization, caching, and
audit. A graph query may answer which inputs and procedures were recorded
without claiming that graph reachability proves semantic correspondence.

**Enabling mechanism:** the useful introspection part of B, restricted to a
descriptive projection over A-owned contracts.

**Promotion condition:** every graph node and edge retains its domain type,
claim strength, checker status, and non-claims; unknown semantic payloads fail
closed for reliance.

### 7.6 Explicit cross-regime migrations

Typed regimes allow a future carrier or semantic evolution tool to produce a
new subject and a separately checked migration relation instead of silently
upgrading bytes. Compatibility can be scoped by subject family, relation, and
consumer rather than one global release number.

**Enabling mechanism:** A-owned domain migration relations, optional D
validators, and no assumption that identity is preserved.

**Promotion condition:** a real retention/release boundary, exact old/new
semantics, supported migration domain, and declared information-loss behavior.

### 7.7 Effect-aware retries and observational comparison

Separating semantic transforms from effectful occurrences enables explicit
staging, atomic publication boundaries, retry identities, cleanup state, and
comparison of two runs without pretending they are one replayed pure
transition.

**Enabling mechanism:** domain-owned event/effect contracts plus narrow live
capabilities.

**Promotion condition:** Stage 4B must define protected operational events,
partial-effect reports, and retry/idempotence semantics per target.

### 7.8 Plan-placement experimentation without identity leakage

The tagged distinction between plan-independent OIR, plan-specialized OIR, and
below-OIR realization plans lets Stage 4B compare granularity, scheduling,
buffering, and supplier strategies. A plan enters `OirId` exactly when
projection reads it; otherwise it remains a realization input.

**Enabling mechanism:** explicit `ProverPlanId` and read-set closure.

**Promotion condition:** an obligation/plan ledger must assign every field to
one earliest semantic transition and prohibit duplicate ambient consumption.

These opportunities are option value, not requirements. None justifies a wire
format, certificate, or shared algebra before its promotion condition is met.

## 8. Preferred architecture hypothesis in operational form

This section makes the recommendation testable without ratifying it.

### 8.1 Shared layer

The project layer owns a review and introspection schema with at least:

```text
stable transition name and family
source, auxiliary-input, and result subject kinds
source, bridge/checker, target, and relying-consumer owners
complete declared read and dependency closure
semantic and checker regimes
procedure/proposer authority
exact claimed relation and protected observers
identity and cache effects
capability mint, narrowing, copying, and degradation behavior
effect class and binding time
qualified success, negative, refusal, unsupported, inconclusive,
  operational-failure, and partial-effect outcomes
recomputation, validation, certificate, re-authentication, and replay class
durable consumer, retention promise, residual trust, and reversal trigger
```

This schema may support generated documentation, completeness lints, graph
views, and API conformance tests. It does not imply:

- one `Transition` runtime sum type;
- one transition identity;
- one wire envelope;
- one checker registry with semantic authority;
- one generic composition law; or
- one result Boolean.

### 8.2 Lifecycle spine

The target lifecycle uses Candidate C's authority model under domain-owned
contracts:

```text
AuthoringUnit
  -> ResolvedAuthoringUnit
  -> CanonicalProtocolCandidate
  -> AuthenticatedCanonicalProtocol
  -> AdmittedProtocol
```

Normalization produces a candidate and may emit diagnostics or an optional
witness. Authentication independently checks physical normal form, typed
semantic identity, and exact dependency closure. Admission checks the
whole-Protocol predicate and mints only process-local immutable authority.
Persistence carries subject bytes and references, never the capability.
Reopen, link, composition, or checked change creates a new raw candidate and
does not inherit output authority.

### 8.3 Per-family mechanism rule

| Transition family | Preferred first mechanism | Escalation or fallback |
|---|---|---|
| Canonical authentication and admission | Direct owner recomputation; local capability | Optional receipt only for a named consumer that cannot cheaply re-admit |
| Persist/decode/re-admit | Transport/schema authentication followed by fresh semantic checks | Compatibility layer only after a concrete retention/release promise |
| Relation-interface admission | Direct relation-owned predicate | Durable result only if another process needs it |
| Relation correspondence | Exact pair/tuple-bound bridge judgment | Edge certificate if independent replay has a real consumer |
| Property analysis | Analysis-owned direct decision or explicit derivation checking | Portable derivation when independent replay is required |
| Compiler/link/normalization proposal | Untrusted or heuristic producer plus named per-result validator when feasible | Direct trusted transform with explicit residual trust when no smaller checker exists |
| Compiler selection | Recompute exact domain, validity, objective, and selection while bounded | Add a domain-completeness witness only if recomputation becomes materially expensive for a named consumer |
| FS instantiation | Deterministic Protocol construction and ordinary target admission | Keep separate theorem-backed `FSCompile` and property-specific transport |
| OIR projection | Exact Interface/role/plan-closed bridge; paired local capability | Source-bound certificate only if source-free independent checking is required |
| Standalone OIR admission | Direct target-local recomputation | Never infer source coverage from local validity |
| Supplier binding | Direct exact-closure checking and local provider capability resolution | A portable binding remains configuration, not live authority |
| Realization | Producer plus target-specific validator when materially smaller | Otherwise name a trusted producer and retain bounded conformance evidence as evidence |
| Deployment and invocation | Domain-owned effect contracts plus scoped live capabilities | Receipts attribute observations; they do not replay effects |
| Evidence, appraisal, reliance | Separate typed transitions under their own policies | No backward semantic authority |

### 8.4 Persistence and identity rule

Persist a domain subject or edge result only when a named consumer needs it to
cross a process, trust, cache, audit, or retention boundary. Give it a
domain-owned identity over its exact claim and inputs. Never introduce a
global `TransitionId`; producer trace identity, certificate identity, target
semantic identity, and operational occurrence identity remain different.

### 8.5 Composition rule

Procedural sequencing uses typed capabilities and input preconditions.
Mathematical relation composition requires an exact relation-owned theorem.
Certificate chaining establishes only the conjunction or composed claim that
is explicitly checked. Protocol composition constructs a new
`InteractiveCore`. Operational sequencing uses causal event and partial-effect
semantics. No adjacency rule crosses these categories.

## 9. Hard constraints independent of final framework choice

Any Stage 2 convergence that violates one of these constraints fails the fixed
Stage 1 entry contract or a cross-candidate falsifier:

1. Semantic subject, production attempt, checked relation, local authority,
   evidence, appraisal, and reliance remain distinct categories.
2. Every normative output is extensionally closed over declared immutable
   inputs, dependency preimages, semantic regimes, and binding-time snapshots.
3. Source, bridge/checker, target, and relying-consumer authorities are named
   separately; a bridge cannot redefine an endpoint or authorize its own use.
4. `ProtocolInterfaceId` and `ProverPlanId` are explicit inputs wherever the
   result reads their fields. Equal `ProtocolId` is not a substitution proof.
5. Serialization, raw copying, FFI transfer, reopening, and mutation never
   preserve a process-local admission or paired-relation capability by
   assertion.
6. Structural legality, identity authentication, semantic admission, target
   local validity, source/target correspondence, property derivation,
   realization, and reliance are different judgments.
7. Every transformation relation names its direction, domain, protected
   observers, assumptions, quantitative loss where relevant, and unsupported
   or inconclusive cases.
8. Successful negative judgments remain successful judgments; typed refusal,
   unsupportedness, inability to answer, operational failure, and partial
   effect remain distinct.
9. A target digest, signature, provenance record, or packaged witness does not
   prove its semantic claim or provide a missing dependency preimage.
10. Source-free OIR establishes only target-local claims unless sufficient
    source-bound evidence and its checker are present.
11. Proposal/search history does not enter semantic target identity unless it
    changes the canonical target; a checked relation never follows from ID
    equality or inequality alone.
12. Semantic composition is relation-specific, Protocol composition is Core
    construction, and effectful sequencing is not modeled as pure arrow
    composition.
13. A durable record, certificate, checker ID, or compatibility promise
    requires a concrete consumer and lifecycle; absence is a valid final
    design choice.
14. A validator must state residual trust and completeness. A sound incomplete
    validator cannot turn unsupported or inconclusive cases into semantic
    refutation.
15. Operational contracts state external effects, publication boundary,
    partial-failure state, retry/idempotence, and residual live authority.

## 10. Remaining falsifiers and evidence gaps

The preferred hypothesis should not be promoted until the convergence pass
either closes or assigns these items:

1. **Catalog enforceability.** Demonstrate that a semantics-neutral shared
   schema can detect missing owners, closures, regimes, identity effects,
   outcome classes, and consumers without becoming a universal semantic type.
   If domain adapters repeatedly disagree, Candidate A needs a stronger common
   executable layer.
2. **Universal consumer search.** Confirm whether build caching, distributed
   compilation, audit, remote checking, or another concrete v0 product truly
   needs a portable heterogeneous transition DAG. If one exists, instantiate
   `B-wire` against its exact query and retention contract instead of rejecting
   it abstractly.
3. **Capability mechanics.** Define copy, borrow, thread, FFI, plugin, lifetime,
   attenuation, and revocation behavior for each local capability family. If
   these cannot be enforced without opaque ambient state, Candidate C loses its
   principal benefit.
4. **Minimal admission closure.** Enumerate the exact immutable basis retained
   by `AdmittedProtocol` and prove that later consumers receive additional
   Interface, Plan, relation, theorem, compiler, or target inputs explicitly.
5. **Validator economy.** For normalization, each compiler family, projection,
   and realization target, compare producer and validator size, semantics,
   dependencies, bounds, and independence. Do not assume D is beneficial.
6. **Private or unavailable inputs.** Identify any claim that must cross a
   boundary after a necessary private dependency or producer environment is
   gone. Such a consumer may justify a purpose-specific proof or may make
   independent replay impossible.
7. **Outcome algebra.** Validate the proposed outcome dimensions against every
   current tool and later operational edge, including negative judgments,
   solver timeout, policy refusal, verifier rejection, and partial effects.
8. **Relation composition.** Identify actual relation pairs that Stage 3 or
   later consumers must compose. State exact laws, observer transport,
   assumptions, losses, and failure domains. Do not infer demand from a graph
   visualization.
9. **Interface closure.** Complete the exact Interface admission and exported
   view needed by Relations and OIR; repeat the relabel/repackaging scenarios.
10. **Plan placement.** Complete the abstract-obligation/plan ledger and decide
    per field whether it changes prover OIR or only realization below OIR.
11. **Long-lived artifacts.** Name any actual retention and independent release
    windows for Protocol, OIR, certificates, supplier bindings, realizations,
    or evidence. Exact-v0 fail-closed handling remains the default otherwise.
12. **Effect boundary.** Later Realization work must show that production,
    deployment, invocation, and evidence recording can report all externally
    visible partial effects without pretending transactional purity.

## 11. Stage 3 pressures

Stage 3 can consume the preferred hypothesis only as a bounded transition
contract, not as a preselected universal implementation. It must resolve the
following Protocol-and-Relations questions before Stage 4 begins:

1. Define the exact closed `InteractiveCore`, `ChallengeInterpretation`,
   `Protocol`, and canonical PIR grammar, including the total observable
   schedule, occurrence namespaces, protected effects, terminal outcomes, and
   abstract endpoint/prover obligations.
2. Define physical canonical-form authentication separately from
   whole-Protocol admission and assign every predicate to one exact side.
3. Define the minimal typed dependency closure and semantic-regime references
   retained by `AuthenticatedCanonicalProtocol` and `AdmittedProtocol`.
4. Define the complete `ProtocolInterface` subject, admission predicate,
   identity encoding, canonical port/occurrence references, and narrow exports
   consumed by Relations and OIR.
5. Define the complete `ProverPlan` subject only to the resolution needed for
   Protocol-owned abstract obligations, plan admission, `PlanRealizes`, and
   the projection-versus-realization placement decision.
6. Define relation-interface ingress independently of optional relation
   artifact interpretation, including exact semantic identity and declaration
   dependencies.
7. Define `RelationCorrespondsAtInterface` over exact Protocol, Interface,
   relation-interface, optional artifact-observation, and regime inputs, with
   affirmative, negative, unsupported, and cannot-answer outcomes.
8. Define `RepresentationEq`, `CoreEq`, `ProtocolEq`, `TraceEq`,
   `TraceRefines`, distributional relations, `FSCompile`,
   `ProjectionCorrect`, `PlanRealizes`, `PropertyTransport`, and
   `IntentionalChange` at sufficient common resolution to prevent generic
   `equivalent` or `preserved` claims. Later owners may complete their internal
   proof languages.
9. Define deterministic FS subject construction separately from the
   theorem/model-backed `FSCompile` relation and property-specific transport,
   including exact occurrence and transcript-prefix maps.
10. Define Core composition as a subject constructor with tagged occurrences,
    face maps, causal seams, one total interleaving, challenge policy,
    transcript domain separation, failure propagation, and new dependency and
    obligation closure. Do not inherit current static-link behavior as the
    semantic definition by convenience.
11. Export explicit transition skeletons and owner/read-set/identity/outcome
    tables to later Analysis, Compiler, OIR, Realization, and Evidence stages.
    Do not prematurely define their complete schemas.
12. State which Stage 3 checks are cheap direct recomputation, which admit a
    smaller validator, which remain trusted, and which have no portable result
    consumer. Do not introduce a common certificate envelope merely to make
    the table uniform.

The clean-room Stage 3 reader should not need current C++ class names, retained
carrier labels, or broad registry objects to infer any semantic contract.

## 12. Candidate recommendation and reversal conditions

This pressure-test pass recommends the following convergence posture:

| Candidate | Recommendation for convergence | Reversal condition |
|---|---|---|
| A: domain-owned typed contracts | Use as the default ownership architecture, strengthened by a shared lintable descriptive catalog | Reconsider if two or more owners cannot maintain compatible closure, outcome, or composition contracts without a central executable type discipline |
| B-local: universal typed algebra | Do not select as the v0 semantic center; retain its useful typed-reference and introspection ideas | Reconsider for a proven subset of pure relations with shared laws and at least one generic consumer that gains more than adapters cost |
| B-wire: universal transition artifact | Do not introduce by default | Reconsider only for a named heterogeneous cross-process consumer, explicit compatibility/retention window, stable relation registry, independent checkers, and demonstrated advantage over edge-specific results |
| C: capability-centric lifecycle | Use for canonical lifecycle and other in-process authority gates; keep relation semantics domain-owned | Reconsider if FFI/distribution needs dominate, authority cannot be enforced without ambient mutable state, or legitimate consumers cannot recheck economically |
| D: producer proposal plus validation | Use selectively where validator economy and consumer need are demonstrated | Reconsider per edge if checking duplicates production, needs hidden/private unavailable state, or no consumer benefits from a durable witness |
| A + C + selective D | Preferred architecture hypothesis for final Stage 2 convergence | Reject if any remaining falsifier above demonstrates a simpler architecture with equal authority precision, better composition, or materially greater option value |

No row ratifies an API, artifact, certificate, identity, or checker. The final
Stage 2 convergence must either confirm the preferred hypothesis with the full
transition catalog or record the evidence that selected a different model.

## 13. Non-claims

- This note is not normative and does not start Stage 3.
- It does not prove any Protocol property, transformation correctness,
  projection correctness, realization correspondence, completeness,
  Fiat--Shamir theorem, endpoint conformance, or evidence sufficiency.
- It does not claim that current compiler replay is implementation-independent
  translation validation.
- It does not claim that an opaque C++ type alone provides a formal capability
  system across threads, FFI, plugins, processes, or languages.
- It does not propose a stable serialized transition, certificate, provenance,
  evidence, or compatibility schema.
- It does not treat current implementation gaps as defects or vulnerabilities.
- It does not use migration cost or current carrier convenience to constrain
  the ideal target architecture.
- Static tests and source paths cited above are bounded correspondence
  evidence; they were inspected but not executed in this pass.
