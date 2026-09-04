# Current-to-target semantic correspondence and gap inventory

> **Document kind:** Temporary Stage 3.4 correspondence and gap inventory
> **Document state:** Complete historical correspondence; absorbed into the
> selected durable target; not a migration plan
> **Authority:** None. The current specifications remain authoritative for
> current intent. The frozen integrated target is the clean-room comparison
> baseline; its selected conclusions have been promoted into non-normative
> durable target owners but have not undergone normative cutover.
> **Current baseline:**
> [`current-protocol-pir.md`](./current-protocol-pir.md) and
> [`current-relations-and-seams.md`](./current-relations-and-seams.md), both at
> the 2026-08-22 repository snapshot
> **Target baseline:**
> [`target-semantic-model.md`](./target-semantic-model.md)
> **Scope:** Semantic correspondence among current objects, fields,
> lifecycles, judgments, and the Stage 3 target roles
> **Non-goals:** This page gives no implementation sequence, migration
> estimate, compatibility promise, code plan, or claim that the current
> implementation realizes the target.
> **Disposition:** The durable target owners and Stage 3 absorption record now
> carry every accepted correspondence and deferral; delete this historical
> inventory with the completed package before authority cutover.

## 1. How to read this inventory

This is a relation between two models, not a rename table.

- **Current** means the intent and implementation correspondence reconstructed
  from the present `docs/spec/`, carrier, tools, and tests. A current
  implementation fact is evidence about what exists now; it has no vote over
  the clean-room target.
- **Target** means the semantic roles selected by the integrated Stage 3 model.
  A target subject is not presumed implemented merely because a current class,
  operation, or document has a similar name.
- **Correspondence** identifies the semantic fact that survives, if any. It
  does not imply byte compatibility, API compatibility, representational
  reuse, or an upgrade path.
- **Gap** names what must be true in the target model that is absent,
  conflated, weaker, contradictory, or deliberately outside the current
  model. It is a design difference, not an implementation task estimate.

The classifications are:

| Classification | Meaning in this page |
|---|---|
| **Retained** | A current semantic invariant remains load-bearing, although its representation or owner may change. |
| **Split** | One current surface has several target owners, identities, or judgments. |
| **Replaced** | The target answers the same question with materially different semantics. |
| **New** | The target introduces a subject or distinction with no first-class current counterpart. |
| **Rejected/conflicting** | A current behavior, ambiguity, or source conflict is deliberately not part of the target. |
| **Deferred** | Stage 3 fixes the seam or signature but leaves the exact later-owned model or conclusion open. |

Rows can have more than one classification. For example, the current total
event order is retained, while the current transcript-token mechanism is
replaced as semantic authority and may remain only a carrier check.

## 2. Architectural correspondence at one glance

```text
current identity-bearing root
  sealed PIR
    = event spine + transcript profile/readings
      + claim graph + policy + construction routes
      + positional content and selected vocabulary

target factored subjects
  InteractiveCore
    = bounded behavior, observations, obligations, failures, terminals
  Protocol
    = InteractiveCore + exactly one challenge interpretation
  canonical PIR
    = the sole v0 production representation of that Protocol

  ProtocolInterface[ProtocolId]
    = external names, containers, positions, codecs, and entry bindings
  ProverPlan[ProtocolId]
    = private construction choices and obligation routes
  Relations subjects
    = external definition reference, interface, instance, binding,
      artifact profile/adapter, optional observation, grounding,
      and correspondence
  construction relations
    = Fresh-to-FS construction and semantic Core composition with exact maps
```

The largest target change is not MLIR removal. The closed MLIR PIR graph
remains the unique physically canonical v0 carrier of a Protocol, with Core as
its embedded authenticated subidentity rather than a second artifact root. The
change is that this carrier denotes a smaller, closed Protocol semantic root,
while Interface, Plan, relation, artifact, construction, and checked-relation
facts become separately owned canonical algebraic values. A satellite may have
one or more transport profiles only through a total tagged lossless decode to
that exact value; such a profile is neither an alternate Protocol carrier nor
semantic authority.

## 3. Protocol and `InteractiveCore`

### 3.1 Root and field correspondence

| Current object or field | Current meaning and implementation correspondence | Target role | Classification and exact gap |
|---|---|---|---|
| `P = (E, <=, A, C, R, chi, K, anchors, B_M)` | Language-independent intent behind the MLIR carrier | `InteractiveCore` plus one `ChallengeInterpretation` forming `Protocol` | **Split, retained, expanded.** Event order, claims, reductions, challenges, and checks survive. Observation classes, dependencies, roles, ports, values, objects, randomness, causal edges, verifier-visible failures, prover-obligation failures, terminals, and distinct endpoint/prover obligations become explicit. Anchors and material bindings no longer serve as a universal relation membrane. |
| One sealed Protocol root | One object combines semantic behavior, construction profile, policy, routes, and carrier identity | `Protocol { core, challenge_interpretation }` | **Replaced.** The target root contains only intrinsic Core behavior and one exact challenge interpretation. Interface, Plan, relation, and construction-result facts are outside it. |
| One event spine and one total order | Block order and transcript token establish deterministic schedule | `events`, `causal_edges`, and one identity-bearing total `schedule` | **Retained, expanded.** The target preserves one total potential-event schedule and adds explicit causal structure. The total order must extend every edge; token threading is not the semantic definition. |
| Absorption subset `A` and per-event `absorbed` behavior | Selects current transcript updates | protected `ObservationClass::Transcript` plus total `TranscriptConstruction.event_actions` | **Split, replaced.** Whether an occurrence is transcript-observed is Core meaning; exact typed atoms, codecs, framing, absorb, derive-challenge, and no-op actions are construction meaning. A Boolean carrier flag cannot stand for both. |
| SSA-like event values | Operations introduce freely readable values | closed fourteen-form pure `ValueNode` DAG with typed domains, origin bindings, and role knowledge | **Retained, strengthened.** The target makes input-port values, constants, private-randomness values, challenge values, prover-obligation outputs, check results, occurrence-exact failure status/occurrence values, tuples, projections, canonical sum injection, total pure calls, canonical guard decisions, and the sole phi-like `GuardedMerge` explicit. `InjectVariant(sum, ordinal, value)` is structural and injective, checks the exact variant payload domain, and has no selected implementation. Canonical order, availability, exhaustive one-hot merge guards, and ambient-read prohibition are admission facts. No v0 event has an ambient ordinary-value result: every effect-originating value uses its named Core constructor, and a new value-producing effect requires a new constructor and Protocol regime. |
| Stage-positioned bindings and implicit return values | Current rows expose values without one general input/output port-binding contract | `PortDecl.binding = InputSource \| OutputValues(CanonicalSeq<ValueRef>)` | **New explicit boundary.** `PortValue` may name input occurrences only. Every output port names exactly one same-domain value per port occurrence, in ordinal order; the grouping itself creates no value, exposure, availability fact, event, or role-knowledge transfer. Direction, visibility, multiplicity, purpose, and value domain cannot be repaired later by Interface or OIR. |
| Abstract SSA-versioned protocol objects | Present in kernel intent; only flat profiled values are carried | `ObjectDecl` under exact `ProtocolObjectContractRef` | **Retained from intent, new relative to carrier.** Object contract, constructor inputs, visibility, and observation surfaces are explicit; mathematical relation meaning remains outside Core admission. |
| Linear claims and source/reduction/sink graph | Exact one-producer/one-consumer claims; current carrier enforces linear use | `ClaimDecl`, `ReductionDecl`, and `CheckDecl` resource graph | **Retained, generalized.** Linear claims remain available, while the target admits an explicit `Persistent` disposition when the regime defines it. Production, use, routing, acyclicity, and closure remain admission facts. |
| Claim profile plus anchor dictionary | Stable Protocol claim descriptor over opaque references | exact `ClaimContractRef` plus typed value/object parameters | **Replaced.** Target claim structure cites exact contracts and typed semantic parameters. Relation interpretation is carried by a separate `RelationBinding`, not inferred from anchor names. |
| Source, reduction, discharge/export/assume/residual operations | Close or route claims under content-pinned contracts and policy | claim/reduction graph, explicit checks, `TerminalDecl`, and later consumer-specific routing | **Split.** Intrinsic claim flow and accept/reject/abort behavior remain Core facts. External export or analysis routing is not an untyped sink-name namespace inside the Protocol. |
| `SealPolicy` embedded in Protocol identity | Normatively spans five policy dimensions; implementation enforces sink permissions only | explicit Core behavior plus external policy or a different wrapper/Protocol when behavior changes | **Rejected/conflicting.** The target has no ambient policy field capable of changing accepted claims, checks, failures, or language without changing the corresponding semantic subject. The current partial policy table is not promoted. |
| Segment starts | Link records concatenated run boundaries and later FS seam obligations | explicit causal seams, interleaving, occurrence maps, and composition context | **Replaced.** Construction history is not intrinsic Core content unless observable. A segment is not a substitute for a checked composition relation or exact transcript context. |
| Implicit final endpoint decision | PIR has no decision event; projection appends OIR `decide` or `finish` | explicit `ReachTerminal` event and `TerminalDecl` | **New relative to carrier, retained from abstract intent.** Accept, reject, and abort are Protocol behavior before projection. |

### 3.2 Current event rows to target occurrences

This table maps meaning, not operation spelling.

| Current carrier form | Target semantic destination | Classification and boundary |
|---|---|---|
| `pir.begin` / `pir.end` | Root framing and schedule completeness, not Core events | **Replaced.** The target has one explicit schedule and fallback terminal; carrier delimiters do not acquire occurrence identity. |
| `pir.bind` | an input `PortDecl { binding = InputSource }`, `PortValue(input_occurrence)`, and, when public observation is semantic, `ObservePublicValue` | **Split.** Input availability belongs to ports and role knowledge; output ports instead group one exact already-available same-domain value per output occurrence in `OutputValues`. The grouping itself creates no exposure. A transcript/public occurrence is explicit rather than inferred from a stage and absorbing bit. External statement labels move to Interface. |
| `pir.slot` | directed `Message(from, to, channel, payload, codec)` occurrence | **Replaced, strengthened.** Sender, receiver, channel, codec, protected observations, guards, failures, endpoint participation, and prover production obligations are explicit. Construction bindings move to Plan. |
| `pir.chal` | `FreshChallenge(ChallengeDecl)` occurrence in Core; Fresh or FS meaning in `Protocol.challenge_interpretation` | **Split.** Distribution, occurrence, causal prefix, and sampling failure are Core facts. Transcript squeeze/sample procedure is a separate construction. |
| `pir.check` | `CheckDecl`, its exact `InvokeCheck` occurrence, and a closed `CheckFalse(check, event)` failure source | **Retained, expanded.** Contract identity and typed inputs remain; the check's `on_false` names one occurrence-exact verifier failure whose effect either terminates or continues with the fixed status token. Opaque execution still does not establish mathematical truth. |
| No general explicit-abort occurrence | `RaiseFailure(FailureRef)` paired bijectively with `FailureSourceRef::ExplicitAbort` | **New.** An explicit abort is an identity-bearing Core occurrence with class `ExplicitProtocolAbort`; it cannot be synthesized from a label, terminal, or checker error. |
| Missing route, missing supplier output, duplicate/early output, or private sampling failure | a complete unique `ProverObligationFailureDecl` family indexed by exact `(obligation, cause)` and runtime `ProverDidNotProduce(failure_ref, partial_state)` | **Split from verifier failure.** Causes are `MissingOutput`, `DuplicateOutput`, `EarlyOutput`, and `PrivateSamplingFailed` over exact output/randomness references. Nonproduction does not invent an accept/reject/abort terminal. Plan admission, `PlanRealizes`, execution nonproduction, and later completeness are separate judgments. |
| `pir.artifact_verify` | ordinary typed objects/values, message or artifact observations, checks, claims, failures, and obligations where those semantics are actually specified | **Rejected as one privileged opaque row; deferred for verifier descent.** The current row bundles unresolved child identity, ABI, proof, route, and semantics. Stage 3 does not grant it recursive-verification meaning. A later wrapper/descent model must bind every required subject explicitly. |
| `pir.reduce` | `ReductionDecl` in the claim resource graph | **Retained, generalized.** Exact inputs, outputs, side inputs, and contract remain structural. The target does not infer a theorem or property from admission. |
| `pir.material_bind` | typed `RelationBinding` maps and separately checked `CommittedObjectGrounding`, or an explicit non-relation value/object binding owned by its contract | **Split, replaced.** Declared digest-shaped equality is too weak to act as relation grounding. Grounding must name the object role, domain, encoding, Interface position, and adapter derivation. |
| terminal sink operations | explicit claim/check interpretation, failures, and `ReachTerminal` | **Replaced.** Termination is behavior, not merely a claim consumer plus policy permission. External residual/export semantics remain later-consumer concerns. |

### 3.3 Behavior newly made explicit

The following target Core facts have no complete current carrier counterpart:

- exactly one Prover, exactly one Verifier, at most one
  PublicEnvironment, and per-role knowledge derivation;
- typed public, private, context, witness, and protocol-value ports with an
  exact `InputSource` or occurrence-ordered `OutputValues` binding;
- pure-value and protocol-object graphs with exact dependency contracts and
  typed origins for randomness, challenges, prover obligations, check results,
  fixed failure-status tokens, occurrence booleans, and exhaustive guarded
  merges, with no generic event-output form;
- private prover randomness, public randomness, joint distributions, and
  correlation groups;
- one closed `EventKind` sum inside a common `EventDecl` occurrence envelope
  carrying the exact actor, inputs, protected observations, and activation
  guard; admission checks `Message.actor == from`, the unique
  PublicEnvironment actor for `FreshChallenge`, verifier ownership of
  `InvokeCheck`, `RaiseFailure`, and `ReachTerminal`, and the named observer or
  emitter for `ObservePublicValue` and `EmitArtifact`;
- bounded branching through guarded occurrences and an unguarded fallback
  terminal;
- first-class verifier-visible failures with the closed `CheckFalse`,
  `ChallengeSampling`, or `ExplicitAbort` source sum, an explicit
  `RaiseFailure` event, terminating or fixed-token status-continuing effects,
  a complete cause-indexed Core-owned prover-obligation failure family, a
  distinct `ProverDidNotProduce` outcome, and explicit accept, reject, and
  abort effects;
- a total operational trace relation that distinguishes inactive events from
  missing active occurrences; and
- complete, type-distinct endpoint and prover obligation sets derived from,
  and checked against, the event vocabulary.

These are **new semantic commitments**, not claims that current MLIR operations
already encode equivalent information.

## 4. Canonical PIR, identity, and dependency closure

### 4.1 Carrier correspondence

| Current surface | Target role | Classification and exact gap |
|---|---|---|
| MLIR as a structural carrier | The unique physically canonical MLIR PIR graph for each Protocol, containing its Core | **Retained and narrowed.** The target keeps MLIR parsing, closed structure, diagnostics, and ecosystem value while defining semantics independently. It does not introduce a separate Core artifact or a second Protocol production language. |
| Current non-Protocol records use implementation-specific in-memory or serialized forms | separately identified canonical algebraic Interface, Plan, Relations, transcript-construction, composition, and checked-result values, with optional lossless transport profiles | **Replaced transport boundary.** A transport must decode totally, with tags, to the exact canonical satellite value. Transport/profile validation, dependency authentication, identity recomputation, and domain admission remain distinct; a JSON, binary, MLIR, or API spelling cannot add semantic fields or become an alternate Protocol carrier. |
| `pir.protocol` open form and `pir.sealed` persisted form | one `pir.protocol` root representing a candidate; authority lives in immutable capabilities | **Replaced.** A serialized operation name does not encode admission authority. Authentication and admission do not require mutating the semantic subject into a different root kind. |
| Fixed current body grammar and operation allowlist | target allowlist rooted at `pir.protocol` and `pir.core`, with dedicated declarations for every Core field | **Replaced.** The target carrier must be bijective with the selected Protocol algebra, so the current bind/slot/chal/tail grammar is not presumed adequate. |
| MLIR verification plus two-pass cross-reference checks | physical canonicality and `Read_R` before semantic admission | **Retained, separated.** Structural parsing and reference integrity are authentication steps; Core and Protocol predicates are domain admission. |
| Token thread plus block position | canonical schedule field and explicit causal edges | **Replaced as authority.** A carrier may use SSA mechanics, but `schedule` and `causal_edges` are the denoted facts. |
| Positional normalization and author-label quotient | typed canonical ordinals and a tiny `CarrierTrivia` quotient | **Retained, tightened.** Only in-memory operation identity and required SSA alpha-renaming are trivia. External names are Interface semantics rather than erased data later read by consumers. |
| Canonical bytes of the current carrier | injective regime-owned `CanonicalEncode` of the semantic value | **Replaced at the identity preimage boundary.** Text, bytecode, printer spelling, host layout, and attribute order are transports. The exact hash primitive and byte grammar remain a later normative choice. |
| Codec, sampler, framing, decoder, and pure-function behavior selected through implementation objects or registry entries | identity-bearing `CanonicalAlgorithmSpec<K>` | **Replaced and closed.** Every algorithm-valued semantic field is either a finite typed total term or a content-addressed contract reference with exact ABI and dependency IDs. Live executable values and checker capabilities never enter semantic identity; referenced specifications are admitted only with their authenticated preimages and closure. |
| `SHA256("zkc/pir\n" \|\| canonical_bytes)` | domain-separated `CoreId`, `TranscriptConstructionId`, and `ProtocolId` over typed semantic preimages | **Split.** The target identity algebra distinguishes intrinsic Core behavior from challenge interpretation and construction. This is not a promise to preserve current digests. |
| Stored sealed id | claimed IDs on the root, recomputed during authentication | **Retained as a check, not authority.** Stored IDs are assertions. Successful recomputation still yields only an authenticated candidate. |
| Human `protocol_name` and author selectors excluded from identity | no human/source names in Core or Protocol; external names in Interface | **Retained and completed.** The target removes the current contradiction in which erased labels are later read as endpoint and relation ABI. |
| Current identity includes construction routes | `ProverPlanId` depends on `ProtocolId`; routes do not enter Core or Protocol identity | **Split, clean break.** Private construction choices have independent semantics and authority. |
| Current identity includes construction profile `kappa` | FS `ProtocolId` depends on `TranscriptConstructionId`; Fresh has its own tag | **Split.** Construction remains identity-bearing but is no longer an undifferentiated profile inside a dual-read Protocol. |
| Current identity includes segment decomposition | target Core identity includes only normalized intrinsic behavior; `CoreCompositionSpecId` and checked maps retain history separately | **Replaced.** Equal normalized Cores may have equal Core IDs even when produced by different composition histories. |
| OIR has a separately computed identity | later OIR remains a distinct derived subject | **Retained boundary, deferred exact schema.** Stage 4B owns OIR identity and projection relations. |
| Seal/parser normalization silently resolves labels, order, defaults, and selected registry entries | `NormalizeAuthoring` plus a capability-neutral `NormalizationAudit` and separately typed Protocol/Interface/Plan candidates | **Replaced front-end boundary.** Every erased distinction is recorded as retained, extracted, proved inside the finite declared quotient, or rejected before erasure. Normalization authenticates or admits none of its outputs. |

### 4.2 Dependency correspondence

| Current dependency mechanism | Target role | Classification and exact gap |
|---|---|---|
| Joint `ProtocolVocabulary` with profile, check, hole, reduction, predicate, and terminal entries | closed `DependencyKind` sum with exact protocol-facing ABIs, including distinct endpoint- and prover-obligation contracts | **Split, replaced.** Protocol dependencies are typed by semantic use. Plan-private dependencies and externally owned relation definitions do not enter the Core dependency sum. |
| String registry ids resolved to content digests | typed content identities and canonical direct manifests | **Retained content pinning, rejected ambient lookup.** Mnemonics cannot discover meaning. The candidate names exact kinds, regimes, IDs, and ABIs. |
| Selected vocabulary tables stamped into sealed PIR while predicate preimages are externally re-resolved | least reachable graph of authenticated dependency preimages | **Replaced.** Admission closes the exact read graph. An ID or partial stamped table cannot authenticate an absent preimage. |
| External `ProtocolEnvironment` required for recheck | exact immutable dependency bundle and admitted capabilities | **Replaced in semantic formulation.** A host may package the bundle, but registry state or process-global lookup is not an unstated input. |
| `kappa` construction registry | exact `TranscriptConstruction` dependencies for suite, codec, framing, and sampling | **Split.** Construction dependencies are authenticated with the construction, not treated as generic Core operations. |
| Live profile methods and registry-selected codecs/functions | closed finite algorithm terms or content-addressed contract references | **Replaced.** Function equality is not host-language pointer or implementation equality. The canonical algorithm specification enters its owner's semantic preimage; a matching executable capability remains a separate checking or execution input. |
| `HoleContract` inside ProtocolVocabulary | Plan-private dependencies and typed holes/supplier requirements | **Moved to Plan.** Hole ABI is not intrinsic verifier-visible Protocol meaning unless a later checked classifier shows that a field changes prover OIR structure. |
| `RelationContract` outside `ProtocolEnvironment` | externally owned `RelationDefinitionRef`, separately admitted `RelationInterface`, `RelationBinding`, and optional artifact adapter/observation | **Retained separation, refactored.** Relation material still cannot acquire Core authority through a dependency ID. |
| Normative source-vocabulary and sealed-table section counts disagree | subject-specific direct dependency manifests and least authenticated closure | **Rejected/conflicting.** Source envelopes, canonical Protocol dependencies, Plan dependencies, and relation subjects are not counted as one overloaded vocabulary object. |
| Current exhaustive identity-domain list omits live value-profile and relation-contract domains | one typed identity preimage and regime per target subject family | **Rejected/conflicting.** Domain separation is part of each identity definition; an unlisted live domain cannot be accepted as an implicit extension. |
| Unknown vocabulary fields and stale digests fail closed | closed dependency-kind sum, exact regimes, and authenticated closure | **Retained.** Adding a Core semantic dependency kind requires a new Protocol semantic regime. |
| Schema or package versioning | typed semantic regimes separate from carrier, tool, and package versions | **New distinction.** A semantic change requires a new regime even if carrier fields can still parse. |

### 4.3 Authentication and admission lifecycle

```text
current
  open PIR --seal--> sealed PIR
  bytes --decode/id check--> DecodedPirArtifact
  decoded + ProtocolEnvironment --recheck--> AdmittedPirArtifact

target
  raw carrier
    --decode + closed root/allowlist/physical checks
    --> unauthoritative ReadUnchecked candidate
    --authenticate exact direct dependency preimages and least closure
    --recompute CoreId and ProtocolId
    --> IdConsistentCanonicalPirGraph + authenticated Protocol candidate
    --CoreAdmissible + challenge-interpretation admission
    --> opaque immutable AdmittedProtocol
```

The capability principle is **retained**: bytes, digests, reports, signatures,
or cloned IR do not carry process-local semantic authority. The target changes
three details:

1. physical authentication and domain admission are named for every
   identity-bearing subject, not only PIR;
2. FS cold admission uses a transaction-scoped `CoreAdmissionWitness` to
   avoid a dependency cycle: Core is authenticated and sub-admitted first,
   the exact referenced construction is then authenticated and admitted
   against that witness, and only then is the FS Protocol admitted; the
   witness is discarded after `AdmittedProtocol` is minted; and
3. `AdmittedCoreView` is an attenuated view derived from an exact admitted
   Protocol, not an independently deserializable official artifact family.

The current `seal` implementation is useful correspondence evidence for the
capability pattern. It does not determine whether the target retains open and
sealed MLIR root classes, and the target model explicitly does not.

`Read_R` is exposed only after physical form, dependency closure, and claimed
IDs have all been recomputed. A diagnostic `ReadUnchecked_R` has no bijection
or authority law. This ordering prevents a parseable wrong-ID graph or an ID-
only FS dependency from entering the authenticated domain.

## 5. Events, observations, randomness, and branching

### 5.1 Schedule and observations

| Current fact | Target fact | Classification and consequence |
|---|---|---|
| One totally ordered observable event spine | one total potential-event schedule extending an explicit causal DAG | **Retained, enriched.** Reproducible identity and transcript order survive; concurrency claims cannot be inferred from omitted edges. |
| Absorbing versus non-absorbing operation classes | event-specific protected observation set | **Replaced.** Transcript, wire, public value, check, artifact, claim, failure, and terminal observations are independently named. |
| Check ordering is block position but non-absorbing | explicit `InvokeCheck`, schedule position, check observation, and false continuation | **Retained and made behavioral.** |
| Failure reason inferred from a failed operation or terminal sink | closed `FailureSourceRef`, occurrence-exact `FailureDecl`, and explicit `RaiseFailure` when the Protocol aborts directly | **Replaced.** Every false check, challenge-sampling failure, and active explicit-abort occurrence owns exactly one linked failure. `ContinueWithStatus` yields only `FailureStatusToken { failure, class }`; no ambient payload or checker exception becomes Protocol data. |
| Slot direction inferred from endpoint projection | one shared directed message occurrence | **Replaced.** Prover send and verifier receive obligations derive from the same typed occurrence. |
| Statement binding stage | typed ports with exact input/output bindings plus optional public/transcript observation events | **Split.** Port role, direction, input sourcing, output value, and availability are intrinsic; external statement layout is Interface. |
| Endpoint coverage derived only for supported rows | explicit complete and separate `EndpointObligation` and `ProverObligation` sets checked by Core admission | **Strengthened.** External participation and prover-produced semantic values have different typed domains; no admitted event may escape either applicable constructor. |
| `artifact_verify` seals without a complete obligation row | no special admission escape | **Rejected/conflicting.** Every target occurrence must close observation, failure, and obligation semantics before Core admission. |

### 5.2 Randomness and challenge meaning

| Current fact | Target fact | Classification and consequence |
|---|---|---|
| Carrier has fresh public `pir.chal` only | every Core challenge is a typed `FreshChallenge` occurrence with distribution and failure; Protocol selects Fresh or exact FS interpretation | **Split.** Occurrence structure is shared while interpretation produces distinct Protocol identities. |
| Abstract origins include fresh, project, derive, imported | Core randomness plus explicit composition `ChallengePolicy` | **Replaced.** Shared child challenges map to exact target challenge bundles. Derived and imported child challenges instead become target values plus explicit `ObservePublicValue` target occurrences and remove their fresh randomness, sampling endpoint obligations, sampling failure, and public-coin index. Derivation uses exact pure source values; import uses a public context port and a PublicEnvironment-owned endpoint obligation, never a prover obligation or hidden fresh-challenge capability. |
| Challenge domain, space, count, sampling rule | `ChallengeDecl`, `DistributionContractRef`, public coin index, prefix template, and rejection/abort mapping | **Retained, made total.** Sampling failure cannot remain an unstated executor outcome. |
| Contract-derived `P_req` and BIND | a Core-owned guarded event-prefix template plus its construction-specific action-wise image | **Retained in stronger form.** The Core template is exactly every prior potentially active transcript-participating Core event in schedule order, not an informally chosen causal subset. The FS construction maps it through total event actions, drops no-ops, and directly checks the resulting absorb/derive prefix. |
| No private-randomness semantics in canonical PIR | `RandomnessDecl` for private prover samples and exact correlation | **New.** A Plan may choose an algorithm but cannot change the declared distribution. |
| One transcript state implied by token chain | active transcript occurrence sequence plus exact construction absorb/squeeze actions | **Split.** Core says what is observed; construction says how typed atoms advance a transcript. |

### 5.3 Bounded branching

The current carrier has one unconditional static sequence. The target adds
finite branching without admitting host-language control flow:

- every event has a pure `activation_guard` over earlier available values and
  check results;
- an inactive event produces no transcript, wire, check, artifact, failure, or
  terminal occurrence;
- `FailureOccurred(f)` is a total Boolean after the exact source resolves,
  while `FailureStatusValue(f)` exists only on the status-continuing failure
  path and carries the fixed `{failure, class}` token;
- `InjectVariant` is the only structural injection into a closed sum domain;
  it preserves the exact variant and payload needed to give heterogeneous
  captured exits one common per-child merge domain;
- `GuardedMerge` is the only phi-like value and requires resolved, pairwise-
  exclusive, exhaustive one-hot guards and path-available branch values;
- execution still scans one total potential-event schedule; and
- an unguarded fallback terminal closes every non-prover path, while an exact
  active prover nonproduction cause yields `ProverDidNotProduce` instead of a
  verifier terminal.

This is **new** target behavior. It must not be retroactively read into current
membership attributes, segment starts, endpoint decisions, or tool control
flow.

## 6. `ProtocolInterface`

### 6.1 Distributed current facts become one dependent subject

| Current fragment | Target destination | Classification and exact gap |
|---|---|---|
| PIR bind author labels | `ProtocolInterface.external_ports`, public-value maps, and external names | **Moved and identity-restored.** External names are Interface identity, never erased Protocol trivia later read by a consumer. |
| OIR `statement_labels` and entry signature | Interface statement-container contract plus later OIR projection | **Split.** Interface fixes external meaning; OIR fixes endpoint program representation. |
| OIR proof row labels and codecs | `proof_container`, proof occurrence map, and exact lossless codecs | **Moved to Interface at the external boundary.** Later OIR may cite the admitted Interface rather than recover it from a PIR presentation. |
| Claim anchors and routed sink names used as application-facing handles | typed `application_bindings` and `external_outcomes`, or Relations-owned binding | **Replaced.** An opaque string in Protocol cannot simultaneously be claim identity, application ABI, and relation map. |
| RelationContract `statement_correspondence` | `RelationBinding.public_port_map` over an exact `ProtocolInterfaceId` | **Split.** Relation-specific interpretation is not Interface content. |
| No current `ProtocolInterfaceId` | dependent identity over Interface regime, exact `ProtocolId`, and canonical Interface | **New.** Several Interfaces may preserve one Protocol while exposing different byte languages or external names. |
| Projection reads labels erased by Protocol identity | projection consumes exact admitted Interface | **Rejected/conflicting behavior.** A function of Protocol identity cannot depend on a representative-only author label. |

### 6.2 Exact preservation boundary

The target closes the Interface at component resolution rather than leaving an
open "mapping" object. Its identity-bearing fields are the exact `ProtocolId`,
external ports with direction/domain/Protocol-port/value-codec bindings,
statement and proof containers, role entries, a lossless statement binding, a
guard-aware bijection from external proof positions to exactly the
proof-channel `Message` occurrences, external outcome bindings, and typed
application bindings. These components are target design; similarly named
current labels, rows, or codecs are only correspondence evidence.

The target Interface may change packaging, names, and external byte language
only through total, injective, lossless maps that recover exactly the Protocol
semantic values and occurrences. It may not:

- restrict or enlarge the accepted Protocol language;
- introduce a semantic default;
- reorder transcript-visible proof occurrences;
- alter canonical message bytes or transcript framing;
- change challenges, checks, failures, or terminals; or
- assert a relation correspondence merely by naming an application role.

Any such change is a checked adapter, external policy, or a wrapper/new
Protocol. This is a **new explicit boundary**; the current distributed surface
does not enforce it as one judgment.

## 7. `ProverPlan`

The target Plan is likewise a closed dependent schema: exact `ProtocolId`,
typed private-input descriptors, a typed construction DAG, typed holes,
authenticated private dependency descriptions, supplier requirements, and a
total route map over the selected prover obligations. Plan value references
are limited to Protocol-available values, Plan inputs, construction outputs,
and hole outputs; private effects are limited to pure work, use of already
Protocol-owned private randomness, or declared supplier requirements. These
component constraints prevent a current runtime handle or provider object from
becoming target semantics by correspondence alone.

| Current fragment | Target destination | Classification and exact gap |
|---|---|---|
| Optional `routes` dictionary inside PIR and Protocol identity | separate `ProverPlan[ProtocolId]` | **Split.** Private construction choices no longer change Core or Protocol identity merely because they are one possible plan. |
| Route witnesses and handle classes | `PlanInput` descriptors or typed supplier requirements; relation witness ports remain Relations-owned | **Split.** A Plan input is not automatically a relation witness assignment, and runtime handles are never Plan semantic content. |
| `HoleContract` instances, parameters, and DAG | typed `ConstructionNode`, `TypedHole`, and Plan-private dependency graph | **Retained structurally, moved.** Exact DAG closure and ABI checks remain Plan admission facts. |
| Carrier prose allows anchored-material/expression references beyond the implemented six route-reference classes | one closed Plan grammar under the Plan semantic regime | **Replaced rather than reconciled by class reuse.** The target admits exactly its declared Plan references and refuses unknown constructors; neither current prose nor current C++ enum silently defines that set. |
| Slot construction binding | `obligation_routes: ProverObligationRef -> ConstructionOrHoleRef` | **Retained and generalized.** Every prover-production obligation, not merely proof slots, can be covered without confusing it with endpoint participation. |
| Seal accepts missing routes; prover projection requires total slot routes | Plan admission is independent; `PlanRealizes` separately checks exact total prover-obligation coverage | **Split judgment.** Well-formed plan, complete structural coverage, projection suitability, and successful execution are different conclusions. |
| Route graph includes supplier ABI but not supplier selection/correctness | `supplier_requirements` and later Realization | **Retained nonclaim, deferred provider semantics.** |
| Current routes enter Protocol identity | `ProverPlanId` commits to Plan regime, exact `ProtocolId`, and Plan content | **Replaced identity boundary.** |
| Current route structures may carry runtime-facing witness handles | Plan preimage contains only semantic descriptors, typed requirements, and dependency references | **Rejected from Plan identity.** Runtime secret values, supplier handles, process-local capabilities, mutable provider state, credentials, and invocation occurrences are resolved only during execution. |
| Current prover projection reads route content directly | Stage 4B checks `PlanSemanticClass` and reports exact read set | **Deferred with a fixed constraint.** Projection-relevant facts may be read only under an exact Plan basis; realization-only fields may not be read by projection. |
| Compiler `TransformPlan` / Soundness `DerivationPlan` | remain Compiler- or Analysis-owned | **Rejected as aliases.** They are not ProverPlans. |

An affirmative target `PlanRealizes` establishes only structural obligation
coverage, exact typed routing, and the syntactic fact that the Plan grammar has
no constructor or reference capable of changing Core events, randomness,
transcript actions, checks, failures, terminals, identities, or accepted
language. It does not establish semantic noninterference of arbitrary code,
value correctness, distributional fidelity, witness validity, supplier
correctness, completeness, termination, cost, performance, acceptance, or
proof production. No current route test or successful prover run is
correspondence evidence for those stronger claims.

## 8. Relations, artifacts, instances, and witnesses

### 8.1 Ontology split

The current `RelationContract` is useful as an evidence ledger but conflates
several target roles. Its target correspondence is therefore a decomposition:

```text
current RelationContract
  + optional bytes
  + one sealed-PIR presentation
  + report

target
  externally owned RelationDefinitionRef
  + admitted RelationInterface
  + admitted RelationInstance for exact public values
  + local confidential PrivateWitnessAssignment
  + admitted RelationBinding[ProtocolInterfaceId, RelationInterfaceId]
  + admitted RelationArtifactProfile and RelationAdapterContract
  + optional RelationArtifactObservation
  + checked RelationArtifactAgreesWithInterface
  + checked CommittedObjectGrounding
  + checked RelationCorrespondsAtInterface
  + checked RelationInstanceCorrespondsAtInterface
  + later-owned RelationSatisfies
```

### 8.2 Current `RelationContract` field correspondence

| Current field | Target role | Classification and exact gap |
|---|---|---|
| `claim_profile` | `RelationInterface.accepted_result` plus `RelationBinding.result_map` to an exact Protocol claim or terminal | **Split.** Coarse claim-profile equality cannot by itself identify the relation result semantics. |
| `relation_anchors` | externally owned `RelationDefinitionRef`, committed-object roles, exact binding maps, and grounding clauses as appropriate | **Split, replaced.** Digest-shaped anchors are not a universal ontology. Each use must say whether it identifies a definition, object, artifact, or public value and which owner authenticates it. |
| `instance_anchors` | `RelationInterface.public_ports`, `RelationInstance.public_values`, and binding to Protocol ports/values | **Split.** Interface shape and one actual assignment have different IDs and admission predicates. |
| `format` | an exact independent `RelationArtifactProfile` plus an exact profile-dependent `RelationAdapterContract` | **Moved to optional artifact interpretation.** Artifact support is deliberately absent from `RelationInterface` identity. Byte syntax and interpreter semantics are independently identified and admitted; neither is mathematical relation identity. |
| `identity.content_digest` | `RelationArtifactByteId` over the admitted profile and exact raw bytes | **Replaced scope.** Exact byte identity is not a caller digest or transport checksum and does not establish relation denotation. |
| `identity.attested_id` and `attestor` | an externally owned `RelationDefinitionRef` only if that owner regime defines and authenticates those semantics | **Deferred to definition owner.** zkc does not convert a generic assertion into relation-definition authority. |
| `instance_encoding` | relation port value-domain contracts, Interface codecs, and binding adapters | **Split.** Mathematical value domain, external byte container, and cross-subject conversion are distinct contracts. |
| `witness_ports` | `RelationInterface.witness_ports` | **Retained as interface shape.** An actual secret assignment is occurrence-local and not implied by the declaration. |
| `statement_correspondence` | typed `RelationBinding.public_port_map` over exact Interface and relation-interface references | **Replaced.** Author labels erased from Protocol identity cannot be judgment inputs. |
| `declared_shape` | RelationInterface semantic facts when definition-owned, or artifact-observed facts when merely parsed | **Split by authority.** A declaration and an observation cannot be silently merged. |
| Whole RelationContract digest | several dependent target identities | **Split.** No one target digest stands for definition, interface, binding, instance, artifact, and correspondence simultaneously. |

### 8.3 Protocol claim and relation-definition correspondence

| Current concept | Target treatment | Classification |
|---|---|---|
| `opaque_relation` / `r1cs` claim profile | Protocol-local exact claim contract and parameters | **Retained only as a Protocol claim shape.** It is not the relation definition. |
| Claim occurrence `{artifact_id, claim_ref}` | exact `ProtocolScopedRef<claim>` | **Retained and typed.** Fresh and FS Protocol occurrences do not share a scoped reference merely because their Core claim ordinal agrees. |
| Opaque anchor membrane | explicit `RelationBinding` proposal plus correspondence checker | **Replaced.** Opacity remains at Core admission, but later semantic agreement is no longer inferred from anchor spelling. |
| Live `relation-direct` predicate that assumes an executable RelationContract entrypoint absent from the closed schema | no target counterpart | **Rejected/conflicting.** Predicate execution requires an exact independently owned check/relation contract; absent fields cannot be supplied by prose or anchor names. |

### 8.4 Instance and witness separation

| Current state | Target state | Classification and exact gap |
|---|---|---|
| Instance interface declared but no typed instance value | `RelationInterface` plus `RelationInstance` containing one canonical value per public port | **New subject split.** |
| Runtime statement values reach OIR without a relation-instance judgment | `ProtocolPublicAssignment` from successful Interface decoding plus `RelationInstanceCorrespondsAtInterface` | **New checked relation.** It compares exact values but neither executes the verifier nor reads a witness. |
| Witness-port declaration | relation-interface witness ports | **Retained.** |
| Route witness labels, OIR handles, and supplier inputs | Plan, OIR, and Realization facts | **Kept separate.** They do not become a relation witness merely by matching a name or count. |
| No witness assignment subject | occurrence-local `PrivateWitnessAssignment` over secret capabilities | **New.** It has no mandatory public content ID, avoiding equality leakage and unsafe persistence. |
| No satisfaction judgment | later-owned `RelationSatisfies(definition, instance, witness, model, assumptions)` | **Deferred signature.** No Stage 3 admission or correspondence result substitutes for it. |

### 8.5 Optional relation artifact interpretation

| Current artifact/report behavior | Target behavior | Classification and exact gap |
|---|---|---|
| Optional bytes passed directly to the CLI | exact raw-byte preimage, exact admitted `RelationArtifactProfile`, and exact admitted `RelationAdapterContract` | **Replaced.** Every semantic read is attributable to separately identified byte syntax and adapter semantics. A transport checksum may protect delivery but enters no semantic identity. |
| R1CS header-only parser | bounded adapter observation of prime, arities, and counts | **Retained as a possible observation, with unchanged nonclaims.** It does not read constraints or establish definition fidelity or satisfaction. |
| `content_digest` and header facts mixed into one report | `RelationArtifactObservation` binding exact raw-byte identity, profile, adapter, observed facts, and unread fields; `RelationArtifactAgreesWithInterface` separately answers an exact nonempty field question | **New identified observation and checked relation.** Interpretation reads no expected relation or Protocol. Observation and comparison therefore have explicit, non-circular subjects. |
| Report emitted without report identity or reusable authority | observation ID only after a completed interpretation; local capability recreated by reauthentication and rerun | **Replaced lifecycle.** Serialized result bytes carry no live adapter authority. |
| Name-selected RelationContract | exact dependent IDs and admitted capabilities | **Rejected/conflicting.** A registry key may locate bytes but is not a semantic input. |
| First matching claim occurrence | exact typed binding and exact claim/result map | **Rejected/conflicting.** Occurrence ambiguity is not resolved by traversal order. |

Only completed interpretation mints an artifact observation. Malformed,
unsupported, refused, and checker-failure operations mint none. A later
completed interface comparison may be negative and retain unaffected
agreements; disagreement is a property of that checked comparison, not of the
raw observation.

### 8.6 Grounding and correspondence

The current relation tool combines several comparisons whose target owners are
distinct:

| Current comparison | Target judgment | Classification and exact gap |
|---|---|---|
| Claim-anchor match | RelationBinding subject selection and exact result map | **Replaced.** Exact typed references replace first-match anchor search. |
| Relation-anchor transcript projection | `CommittedObjectGrounding` or an explicit adapter-derived clause | **Retained only when stated exactly.** The map, retained-bit bound, object role, and Interface position must be named. |
| Instance-anchor material wiring | public-port binding plus instance-level correspondence | **Split.** Structural mapping and one public value assignment are separate. |
| Statement label existence | Interface map and typed `RelationBinding.public_port_map` | **Replaced.** Labels are authenticated by Interface, not by a PIR presentation outside Protocol identity. |
| Header arity and declared count agreement | exact-field `RelationArtifactAgreesWithInterface` result, optionally requested by structural correspondence | **Retained as consistency evidence.** A raw observation cannot assert the agreement. |
| Witness count agreement | exact-field artifact/interface comparison only | **Retained with narrow scope.** It is not witness assignment or satisfaction. |
| `computed`, `cross_checked`, `asserted`, `disagreed` arrays | observed facts, field-level agreements/disagreements, residual obligations, and qualified operation outcomes | **Split, refined.** An assertion is an explicit premise or residual obligation, not an affirmative computed fact. |
| Relations checks every declared relation anchor while current Soundness counts only anchors literally named `contract` | exact typed binding/grounding capabilities and consumer-declared Analysis read sets | **Rejected/conflicting.** No property term is selected by an anchor spelling heuristic; a later rule must name the exact grounded objects, model, and assumptions it reads. |
| One correspondence report with an implicit full read set | an exact nonempty `CorrespondenceQuestion`, `RelationCorrespondsAtInterface`, and optional `RelationInstanceCorrespondsAtInterface` | **Split.** The question fixes which clauses may be claimed and which supporting capabilities are required; reusable structural correspondence and one assignment-level comparison have different subjects. |

An affirmative `RelationCorrespondsAtInterface` establishes exact agreement
for every clause in its recorded question and no unrequested clause. Requested
artifact or grounding clauses require their exact prior checked capabilities;
a missing or mismatched basis yields `CannotAnswer`, while a negative artifact
comparison makes that requested clause negative and preserves unaffected
facts. Even a full affirmative does not establish definition truth, instance
truth, witness possession, satisfaction, admission of a different subject, or
any cryptographic property.

## 9. Fresh-to-Fiat--Shamir correspondence

| Current surface | Target surface | Classification and exact gap |
|---|---|---|
| One sealed Protocol has both fresh and duplex-runner readings | distinct Fresh and FS `ProtocolId`s over one `CoreId` | **Split.** Challenge interpretation is identity-bearing. |
| Embedded `kappa` construction profile | separate `TranscriptConstruction` scoped to an exact Core | **Replaced subject boundary.** It owns domain-separated initialization, static application domain, an exact public-context-port map, typed atom codecs, framing, one total transcript action per event, challenge prefixes, a total `ChallengeRef -> FailureRef` abort map, and the closed `Standalone \| Composed(...)` composition context. |
| Challenge domain/space and OIR squeeze | Core occurrence/distribution plus construction-specific squeeze/sample rule | **Split.** Projection no longer creates the semantic distinction. |
| Statement/reduction BIND requirements | exact occurrence maps and directly recomputed guarded transcript-action prefixes | **Retained, strengthened.** Every active transcript event has exactly one absorb, derive-challenge, or no-op action; a challenge is never ambiguously both absorbed and squeezed. Each stored challenge prefix equals all prior potentially active transcript actions in schedule order and reduces to their active runtime subsequence. |
| Binding Lemma stated over the current runner | later `FSCompile` judgment over admitted source, target, exact construction maps, theorem/rule, model, assumptions, and losses | **Deferred theorem seam.** Construction is not security. |
| `StateRestorationToFiatShamirDuplex` adds property-specific error terms to one Protocol claim | Analysis-owned property transport from a checked FS construction | **Reframed and deferred.** Existing formulas are research input, not a general construction relation. |
| Backend transcript conformance not established by construction profile | independent target admission and later endpoint/conformance evidence | **Retained nonclaim.** |
| No source/target occurrence maps | `CoreMap`, `ProtocolMap`, event, challenge, and transcript-prefix maps | **New.** Equal inner Core ordinals do not erase the Fresh/FS scoped-subject distinction. |
| Construction availability tied to theorem discussion | target FS Protocol admission independent of `FSCompile` support | **Replaced.** Removing a theorem basis makes analysis unavailable; it does not invalidate an otherwise admitted target Protocol. |

The construction initialization binds `CoreId`,
`TranscriptConstructionId`, the exact static application domain, and a
canonical map from public Core context ports into initialization actions rather
than `ProtocolId`, avoiding a circular Protocol identity preimage. Runtime
session values flow through those ports and do not create one Protocol identity
per invocation. The construction body represents self-binding with the closed
`BindConstructionSelfId` instruction; authentication computes the construction
ID from that body and execution interprets the instruction using the computed
ID, so the preimage does not contain a literal self-reference.

`ExactCompositionContext` is identity-bearing construction data, but its
formed-Core adequacy is not guessed while the composite Core is still absent.
`Standalone` binds no composition history. `Composed` binds exactly one
authenticated `CoreCompositionSpecId`, the ordered durable child occurrences,
and a total map for every public target context port used by initialization;
it cannot read a private port or infer composition from ambient state. The
construction's total `abort_map` must map every challenge occurrence to that
challenge's linked `ChallengeSampling` failure, so no construction-only
verifier failure exists.
Ordinary construction admission checks it against an exact Core witness/view.
When composition chooses an FS target, `ConstructAndSubadmitCore` first
produces and sub-admits the Core; `FormAndAdmitProtocol` then validates the construction's
composition context against that formed Core and exact context-port map before
authenticating/admitting the construction and the enclosing Protocol. Neither
child FS status nor ambient composition history supplies this input.

## 10. Composition and current `link`

### 10.1 Semantic correspondence

| Current `link` behavior | Target composition role | Classification and exact gap |
|---|---|---|
| Consumes two open PIRs and emits a new open PIR | `CoreCompositionSpec` over admitted child Core views, independently admitted target Protocol, and checked `CoreComposition` maps | **Replaced lifecycle.** Authoring assembly may propose a spec but cannot mint semantic authority. |
| Namespace prefixes distinguish faces | local child slots, later durable `ChildOccurrenceRef`s, and typed child-to-target maps | **Replaced.** Repeated equal child IDs remain distinct without putting arbitrary author prefixes in Core identity. |
| Exact export/source descriptor fusion | one deterministic `LocalTypedFaceMap` per child slot plus claim/resource closure | **Retained concept, generalized.** Roles map only to the unique target role of the same class. The total port map selects exact external/internal input/output forms, preserves role, visibility, domain, multiplicity, purpose, availability, and output producer, and adds acyclic internal feed edges. No free face policy, direction reversal, visibility weakening, alias default, or obligation rename survives. |
| Concatenated schedules and segment starts | one explicit interleaving that extends child schedules, child causal edges, and seams | **Replaced.** Concatenation is one possible specification, not the universal composition law. |
| Axis-wise `kappa` merge | deterministic dependency union plus an independently selected target Fresh or FS interpretation | **Replaced.** There are no dependency- or obligation-merge policy fields. Dependencies are the canonical union of exact child and local preimages keyed by kind, content identity, and Protocol ABI; unequal preimages/ABIs reject. Endpoint obligations, prover obligations, and prover-obligation failures are recomputed from the constructed target and must equal the fragment. Child challenge interpretations are not inherited. |
| Challenge-domain prefixing; normative imported/seam obligations partly absent in code | total per-occurrence whole-bundle challenge policy: independent, shared, derived, or imported | **Replaced and completed.** Independent/shared policies name complete target challenge bundles. Derived/imported child challenges map to target values and exact `ObservePublicValue` occurrences and explicitly remove the fresh randomness, public-sampling obligations, sampling failure, and coin index. Imports use an exact public context port and PublicEnvironment endpoint obligation, not a prover obligation. Failure-policy ownership must agree with the selected challenge disposition exactly. |
| No composition rule for private prover randomness | total complete-bundle private-randomness policy: preserved independent, joint group, derived private value, or external private supply | **New.** Preserve/joint policies name exact target randomness/value/owner-obligation/failure bundles. Derived/external policies remove the child randomness declaration, its exact occurrence in the owner obligation, and its matching `PrivateSamplingFailed` declaration exactly once before substituting the value. Shared types or suppliers never imply independence, equality, or correlation. |
| Current link embeds child failures and terminal sinks in a concatenated body without a general early-exit algebra | separate total `FailurePolicy` and `ReachExitPolicy`, exact suffix suppression, `ExitStatusInjection`, and one typed terminal combiner | **New.** Every verifier failure and every `ReachTerminal` occurrence has exactly one independently typed policy. Propagation terminates; capture produces an exact raw status, injects it into a distinct variant of one common per-child sum domain, and suppresses the rest of that child's potential suffix. Per-child exhaustive `GuardedMerge` inputs over those injected statuses feed one exact result function and one-hot/exhaustive static terminal routes. Capture or a changed failure effect is intentional change, not preservation. |
| Current link can synthesize only the fields representable by its fixed operation grammar | complete local target fragment covering every Core family | **Replaced.** Dependencies, roles, ports, values, objects, randomness, events, causal edges, claims, reductions, checks, verifier failures, terminals, both obligation kinds, and prover-obligation failures use typed local target references before target identity exists. Ambient defaults and cyclic global-looking target references are forbidden. |
| Consumer policy chosen for the composite | explicit target Core behavior and composition spec | **Rejected/conflicting.** No child policy is silently selected as target authority. |
| Route graph namespaced and composed with Protocol | Plan remains a separate subject | **Split.** Core composition does not imply a composed ProverPlan or `PlanRealizes`. |
| Material references preserved/reindexed | typed value/object maps and separately checked relation grounding | **Split.** A shared digest string is insufficient grounding authority. |
| Rejudges the open composite and later reseals it | admits the composition spec against exact live child views, constructs and authenticates a Core candidate, retains only a transaction-scoped Core admission witness, explicitly supplies Fresh or a construction candidate plus exact FS dependencies/checker authority, independently admits the enclosing Protocol, then rechecks exact maps | **Retained independent-target principle, strengthened.** Core is not an independently persistent admitted root. For FS, formed-Core composition-context validation precedes construction/Protocol admission. Challenge interpretation is not a hidden spec or constructor default. Provisional maps and transaction witnesses are discarded. |
| Inputs remain intact | immutable child admitted views retained by checked result | **Retained.** |
| No security-composition theorem | property composition remains Analysis-owned | **Retained nonclaim.** Structural composition never proves soundness, zero knowledge, completeness, or knowledge. |

### 10.2 Identity and law boundary

The target separates:

- intrinsic `CoreId`, computed from the normalized target Core;
- `CoreCompositionSpecId`, which records ordered child IDs, occurrence slots,
  target Protocol regime, deterministic faces, seams and interleaving,
  challenge/private-randomness/failure/reach-exit policies, suffix and terminal-
  combiner data, and the complete local target fragment; and
- a checked `CoreComposition` result retaining exact child-to-target maps and
  admitted views.

The specification identity is not a prose digest of those ideas. Its exact
preimage is:

```text
CoreCompositionSpecId = H(
  "zkc/core-composition-spec",
  CompositionRegimeId,
  target_protocol_regime_id,
  CanonicalEncode(children, face_maps, causal_seams, interleaving,
                  challenge_policy, private_randomness_policy,
                  failure_policy, reach_exit_policy,
                  terminal_combiner, target_fragment))
```

Thus the regime, ordered child IDs and occurrence slots, and every local
composition choice are authenticated without placing the resulting global
target identity inside its own preimage.

Two construction histories can therefore produce the same `CoreId` while
remaining distinct specifications and map results. Conversely, behavioral
equivalence does not imply equal Core IDs.

No universal associativity, commutativity, idempotence, or identity law is
introduced. Repeated use of the same child is not idempotent. Likewise,
`FS(compose(children))` is not presumed equal or related to
`compose(FS(children))`. Any such relation requires exact subjects, maps,
observers, and a later-owned judgment.

The exact capture and terminal equations are identity-bearing and checked, not
executor convention:

- `CaptureFailure.exit_taken` is
  `FailureOccurred(the mapped target failure)`;
- `CaptureReach.exit_taken` is the mapped activation guard of the captured
  `ReachTerminal` event;
- every later guard of that child is the mapped original guard conjoined with
  the negation of the disjunction of all earlier captured exits;
- every captured failure or reach owns one `ExitStatusInjection` whose
  `raw_status` is the exact named capture value, whose `sum_domain` is the one
  canonical disposition sum for that child, and whose `injected_status` is
  exactly `InjectVariant(sum_domain, variant_ordinal, raw_status)`;
- that child sum has one distinct, correctly typed variant for every captured
  reach-status tuple and failure-status token, and every such captured status
  appears exactly once;
- each terminal-combiner input is one exhaustive one-hot `GuardedMerge` for
  exactly one child, with the corresponding injected statuses as branch
  values and their exact `exit_taken` values as branch guards, so all branches
  have that common sum domain;
- `result_value = Apply(result_function, inputs)` and the function codomain is
  exactly the declared nonempty `result_domain`; and
- every non-last final guard is equality with its result tag, while the last
  unique fallback is the residual tag; its `TerminalDecl.result` equals the
  tag and its event is exactly `ReachTerminal` for that terminal.

## 11. Authority, outcomes, and persistence

### 11.1 Authority correspondence

| Current fact | Target fact | Classification and exact gap |
|---|---|---|
| `DecodedPirArtifact` authenticates transport/shape/id but not registry semantics | authenticated candidate without admission authority | **Retained.** |
| `AdmittedPirArtifact` is immutable and process-local | `AdmittedProtocol` and purpose-specific attenuated views | **Retained, generalized.** Every subject owner defines its own admitted capability. |
| Current sealed operation and stored id | raw carrier assertion | **Retained non-authority rule.** |
| Relation CLI structurally loads a contract but emits no reusable admitted result | admitted RelationInterface/Binding subjects and checked local result capabilities | **New lifecycle.** |
| Current report intended to be canonical/digest-consumed but implementation lacks identity and admission | artifact observation may be identified; other checked results persist only for a named independent consumer | **Replaced persistence rule.** Not every useful result becomes a global artifact. |
| `link` returns an open composite | proposal/candidate until target Protocol admission and map checking | **Retained caution, stronger boundary.** |
| Current consumers often reconstruct views from admitted PIR | owner-defined narrow immutable views with adequacy predicates | **New explicit discipline.** No universal fact root is shared. |

### 11.2 Outcome algebra

The current relation specification and implementation disagree over whether a
field mismatch is refusal or a negative judgment. The target resolves the
category error with owner-defined qualified outcomes:

```text
Affirmative
Negative(reason, retained_facts)
Unsupported(exact unsupported construct or question)
CannotAnswer(missing named semantic input or basis)
Refused(missing authority or prohibited invocation)
Malformed(exact structural or framing defect)
CheckerFailure(operational failure, no semantic conclusion)
```

The correspondence is:

| Current behavior | Target classification |
|---|---|
| Completed comparison finds disagreement | **Negative**, retaining unaffected agreements |
| Unknown relation/artifact form | **Unsupported**, not false |
| Missing theorem, model, exact instance, adapter, or other named basis | **CannotAnswer**, not negative |
| Missing admitted capability or prohibited cross-boundary call | **Refused** |
| Broken bytes or structural candidate | **Malformed** |
| Crash, timeout, internal error, or unavailable checker execution | **CheckerFailure**, no semantic result |

This is **replaced semantics**, not a reinterpretation of current CLI exit
codes. Each predicate may use only the subset appropriate to its domain.

### 11.3 Persistence correspondence

Official persistence remains admission-gated. After process, FFI, mutation,
serialization, or reopen boundaries, authority must be recreated by the owning
checks. Target identities name semantic subjects; `RelationArtifactByteId`
names exact raw bytes under an admitted profile; transport checksums protect
delivery only; capabilities grant local authority. None substitutes for
another.

The Stage 3 artifact observation receives an identity because Relations
checkers must replay artifact/interface comparisons across process boundaries
and Stage 6 Evidence may ingest the observation with its later checked
comparison. Correspondence, construction, and other checked results become
durable only when a concrete cross-process consumer justifies their schema.
This avoids turning every intermediate fact into a universal evidence root.

## 12. Later consumers and deferred boundaries

Stage 3 fixes what later layers may consume, but does not design those layers
here.

| Later owner | Current correspondence | Target input boundary fixed by Stage 3 | Explicitly deferred |
|---|---|---|---|
| Relations | relation CLI reads a broad sealed soundness view, labels, contract, and optional bytes | narrow Protocol view plus exact Interface, RelationInterface, RelationBinding and question; artifact work additionally consumes admitted profile/adapter, admitted observation, exact checked artifact comparison when requested, and grounding when requested | satisfaction evaluator/model, additional definition/artifact languages, verifier descent |
| Analysis | current Soundness operates on Protocol claims and ad hoc projected facts | admitted Protocol views; exact question, semantic model, assumptions, occurrence/construction/composition maps; Interface or Plan only when actually read | exact property ontology, theorem schemas, probability/advantage calculus, formal-model adequacy, FSCompile and PropertyTransport conclusions |
| Compiler | checked current transforms and preservation obligations | admitted predecessor facts, declared transformation relation, exact objective inputs, and independently admitted target | Stage 4A candidate/relation/selection schema, property-preservation rules, optimization model |
| OIR | current projection consumes admitted PIR and also representative labels and embedded routes | admitted Protocol plus exact Interface; verifier projection never consumes Plan; prover projection may consume exact Plan only under checked classification | Stage 4B OIR algebra, projection relation, local validity, exact Plan read placement |
| Realization | current suppliers, executors, emitters, conformance, and run records | admitted OIR and explicit provider/input dependencies | provider semantics, machine/backend realization, operational evidence schemas |
| Evidence | current tests, reports, status claims, and run records | separately identified claims, inputs, regimes, checker identity, outcomes, and residual trust | evidence packaging, review workflow, acceptance gates, production readiness |

Additional deferred relations remain deliberately separate:

- `RelationSatisfies`;
- `FSCompile`;
- `PropertyTransport`;
- `ProjectionCorrect`;
- `LocalOirValid`;
- observer-indexed Core, Protocol, trace, and distribution equivalence or
  refinement;
- cost and optimization relations; and
- recursive child-verifier/descent semantics.

None may be inferred from Stage 3 structural admission, construction, binding,
grounding, or correspondence.

## 13. Classification summary

### 13.1 Retained foundations

- a language-independent Protocol meaning represented by MLIR rather than
  defined by MLIR implementation classes;
- a closed, fail-closed canonical carrier;
- one identity-bearing total event schedule;
- explicit transcript-sensitive occurrences and challenge dependencies;
- linear claim-accounting as an available discipline;
- content-pinned semantic dependencies;
- exact canonical identities rather than nominal registry authority;
- independent authentication and semantic admission;
- immutable process-local capabilities at consumer boundaries;
- opaque Core treatment of external relation meaning;
- evidence tiers and narrow nonclaims for relation artifact reading; and
- independent target admission after construction or composition.

### 13.2 Split current surfaces

- current Protocol into `InteractiveCore`, challenge interpretation, and
  separately identified construction;
- current erased/interface-read labels into Protocol trivia versus Interface
  identity;
- embedded routes into ProverPlan plus `PlanRealizes` and later placement;
- RelationContract into definition reference, interface, binding, instance,
  artifact profile, adapter, observation, grounding, and correspondence;
- one relation report into artifact interpretation, exact-field artifact
  comparison, question-scoped structural correspondence, and value-level
  instance correspondence;
- material anchors into typed claim parameters, object grounding, and explicit
  adapter maps;
- current link output into composition spec, target Core/Protocol, and checked
  child-to-target relation; and
- construction facts from property-specific FS theorems and transports.

### 13.3 Replaced or rejected semantics

- reading representative-only PIR labels after those labels were erased from
  Protocol identity;
- using an embedded policy whose semantic dimensions are incompletely
  enforced;
- treating a digest-shaped anchor as definition, instance, object, and
  authorization at once;
- resolving a semantic judgment by registry name;
- selecting the first claim occurrence whose anchor names happen to match;
- conflating disagreement, malformed input, unsupported scope, absent basis,
  refusal, and checker failure;
- treating `artifact_verify` as meaningful before its observation, failure,
  obligation, and child-authority semantics close;
- inheriting child FS status or consumer policy through static link;
- putting arbitrary composition history or author namespace into intrinsic
  target Core identity; and
- treating construction, correspondence, execution, or a passing test as a
  cryptographic or satisfaction conclusion.

### 13.4 Newly introduced target subjects or checks

- `CoreId` and typed Core references under one official Protocol artifact
  topology;
- explicit role knowledge, direction-bound input/output ports, private
  randomness, correlation, guarded branching, closed verifier-failure sources
  and `RaiseFailure`, fixed status tokens, the complete cause-indexed prover-
  obligation failure family, terminals, protected observations, and distinct
  endpoint/prover obligations;
- typed effect-origin bindings, `FailureOccurred`, canonical `InjectVariant`
  sum injections, and exhaustive one-hot `GuardedMerge` in the pure value
  graph;
- `ProtocolInterface` and its preservation admission;
- `ProverPlan` and structural `PlanRealizes`;
- `RelationInterface`, `RelationInstance`, occurrence-local private witness
  assignment, and `RelationBinding`;
- identified `RelationArtifactObservation`;
- identified `RelationArtifactProfile` and `RelationAdapterContract`, plus
  checked `RelationArtifactAgreesWithInterface`;
- checked `CommittedObjectGrounding`, structural correspondence, and
  instance-level correspondence;
- separate Fresh and FS Protocol identities with explicit occurrence/prefix
  maps and total event-action transcript construction;
- `CoreCompositionSpec`, deterministic face and dependency/obligation closure,
  whole-bundle challenge and private-randomness policy with exact removal,
  separate failure/reach-exit policy, suffix/status-injection/merge/terminal
  equations, complete local target fragment, explicit challenge-interpretation
  input, and checked `CoreComposition` maps;
- identity-bearing closed algorithm specifications rather than ambient live
  codec, sampler, framing, decoder, or pure-function implementations;
- unauthoritative `NormalizationAudit` at the authoring-erasure boundary;
- typed semantic regimes, local/global reference discipline, narrow views,
  and view adequacy; and
- qualified outcome classes.

## 14. Exact non-migration conclusion

The current system and the target share several deep architectural instincts:
closed semantic content, a deterministic schedule, explicit transcript and
claim structure, content-pinned dependencies, fail-closed admission, opaque
relation meaning at the Protocol boundary, and process-local capability
authority. Those retained invariants explain why the target can still use a
canonical MLIR PIR and why current implementation evidence remains valuable
research input.

The target is nevertheless a semantic redesign, not a completion obtained by
filling a few current fields. It changes the subject factorization, identity
algebra, event and failure model, dependency closure, Interface and Plan
ownership, relation ontology, Fiat--Shamir construction boundary, composition
relation, outcome algebra, and persistence discipline. Similar names in the
current code do not establish implementation correspondence to those target
roles.

This inventory intentionally stops there. It neither orders the differences,
estimates them, selects compatibility mechanisms, nor recommends how code
should move. Its sole purpose is to ensure that convergence and later Stage 4
work begin from explicit semantic differences rather than accidental current
class boundaries.
