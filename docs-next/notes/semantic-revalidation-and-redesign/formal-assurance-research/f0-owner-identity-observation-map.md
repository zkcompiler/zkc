# F0 Owner, Identity, and Observation Map

> **Kind:** Temporary reconstruction and design-pressure dossier
> **State:** W0 reconstruction and first W1 closure complete; scenario
> falsification remains active
> **Authority:** None. Current facts defer to `docs/` and implementation;
> target facts defer to the cited `docs-next/` owners. Candidate names in this
> page are not selected public schemas.
> **Observed:** 2026-09-02

## 1. Result of the first reconstruction

The selected target does not have a missing semantic center. It already has
identified admitted subjects, exact owner-defined views, closed read manifests,
source-authority bindings, typed noncompletion, Analysis propositions,
translation contracts, validation bases, and residual-trust accounting. No
source-semantic fact needed by the first formal scenarios has yet required a
new top-level owner or a change to `InteractiveCore`.

The missing assurance edge is more specific:

```text
exact owner-admitted subjects
  -> exact selected source closure
  -> independently consumable reified source
  -> checked correspondence to a provider formalization
  -> checked theorem truth and applicability
  -> qualified property-specific Analysis judgment
```

The current implementation stops before that edge. Its formalization receipts
authenticate selected theorem-environment facts and record authored coverage;
they do not check that a formal term denotes one exact zkc subject.

The first design implication is therefore **not** “make Lean the Protocol
owner.” It is to determine whether the existing owner-view and Analysis
machinery can support a complete reification/correspondence family and, under
F0's explicit independently released formal-consumer scenario, a stable
neutral source package. If that product scenario is not selected, the same
architecture has a local view-only mode. Any package must be inert evidence,
not a second source of Protocol authority.

## 2. Current implementation seam

The authoritative current chain is:

```text
SoundnessCatalog rule and binding
  + DeclarationAnnotation
      + source anchors
      + FormalizationReceipt or surveyed absence
  -> freezeSignature shape and slot checks
  -> optional pinned ArkLib build, #check, and #print axioms drift check
```

`FormalizationReceipt` retains repository, revision, declaration, normalized
printed statement, axiom profile, state, human-authored `covers` and
`does_not_cover`, and unmatched rule slots. `freezeSignature` checks annotation
totality, state/axiom consistency, and that unmatched slots exist. The external
driver checks the exact ArkLib pin, builds the declaring modules, reruns
`#check` and `#print axioms`, and compares statement and axiom sets.

This is useful provenance and environment authentication. It deliberately
cannot:

- discharge a Soundness Kernel premise;
- establish that a theorem subject denotes a Core, Protocol, reduction
  occurrence, relation, or run;
- establish theorem applicability to an interleaved or shared-challenge group;
- establish that the native rule computes the theorem's conclusion; or
- transport any property to OIR, a backend, or deployment.

The exact current gap is the human-authored arrow:

```text
zkc rule/occurrence  -- "covers" prose -->  external formal declaration
```

F1 must replace one bounded instance of that arrow with a formed proposition
and an independently checked result. Existing receipts can then become inputs
to theorem-environment validation rather than being discarded.

## 3. Target owner map

| Owner | Identity-bearing subject | Exact source mechanism relevant to formal work | What a formal consumer may use it for | What it does not establish |
|---|---|---|---|---|
| Foundation and profile owner | semantic regime, profile, declaration and law references, evaluator contract | authenticated profile/declaration handles and closed catalogs | decode types, laws, algorithms, and result families under one exact regime | truth of a law, correctness of an evaluator, or cross-profile equivalence |
| PIR | `InteractiveCore`, `Protocol`, invocation, transcript construction, admitted owner handles | `PublicBindingView`, `StrategyDecisionView`, `PublicCoinView`, `EffectView`, `ClaimReductionView`, Protocol `ExecutionView`, construction-family views, `PIRStaticViewReadManifest`, required-read closure, and owner-local source binding | reconstruct schedule, effects, values, visibility, challenges, transcript interpretation, Oracle lifecycle, claims, reductions, terminals, failures, and execution laws | relation satisfaction, cryptographic security, theorem truth, compiler preservation, or endpoint realization |
| Interface | `ProtocolInterface` and exact invocation/transport assignments | owner view coordinate, closed owner read manifest, exact projection and source authority | bind external statement, transport, completion, codec, and invocation roles when the theorem concerns an externally callable contract | honest-prover behavior, witness truth, or protocol security |
| Plan | `ProverPlan`, `PlanRealizes`, and `PlanWitnessSurface` | admitted Plan views plus process-local causal witness surfaces and capabilities | state an honest strategy, private-material role, randomness/state discipline, or witness-grounding claim | adversarial strategy quantification; replay data cannot fabricate causal generation or secret authority |
| Relations | `RelationDefinition`, `RelationInstance`, `RelationSemanticModel`, refinement and correspondence questions | exact definition views, relation/run grounding views, correspondence manifests, owner-source bindings, and `CheckedCorrespondence` | state public instance/private witness/Oracle statement/phase-input roles, satisfaction, model correspondence, refinement, and Protocol-to-Relation occurrence maps | cryptographic advantage, theorem applicability, or a property's truth |
| Analysis | question, goal, proposition, source profile, semantic manifest, support, semantic basis, validation basis, derivation, judgment, policy, and capability | typed source slots, exact owner read manifests, translation contracts, checker contracts, theorem-source validation, residual-trust DAG, and qualified outcomes | own formal-interpretation and theorem-applicability propositions, validate a provider result, retain assumptions, and mint a property-specific capability | source-subject admission, relation ownership, compiler transition, or realization |
| Compiler | `TransformProblem`, `TransformIntent`, admitted targets, semantic paths, transition cases, candidate/domain/decision subjects | exact owner-result bindings, property requirements, protected observers, relation direction, maps, checked transitions, and qualified Analysis inputs | require a property-specific preservation/refinement result and use it under one decision policy | create Protocol admission, infer theorem truth, or treat producer evidence as transition authority |
| OIR and Realization | admitted endpoint program, projection and target-specific realization subjects | projection contracts, conformance tiers, future target validator/model bases, explicit residual trusted-producer boundary | state and check endpoint projection or target realization after those stages activate | follow automatically from PIR admission, a formal Protocol theorem, build success, or fixture parity |

The map has an important negative result: **Plan is not a mandatory input to
every formal Protocol theorem.** It enters only when the proposition concerns
honest strategy realization, witness grounding, private randomness/state, or a
specific implementation. Similarly, Interface enters only when external ABI or
invocation meaning is in the proposition. A universal package that always
copies both would conflate optional owners and leak irrelevant private shape.

## 4. Observation closure by assurance question

### 4.1 Static Protocol interpretation

The minimum static source closure for a whole-Protocol interpretation is:

```text
exact admitted Protocol and Core
  + EffectView
  + PublicCoinView
  + ClaimReductionView
  + ExecutionView
  + every selected construction-family view
  + required profile declarations and law references
```

`EffectView` supplies occurrence order, guards, types, producers, messages,
Oracle actions, checks, terminals, and extensions. `PublicCoinView` supplies
challenge domains, correlations, reduction use, and public-condition closure.
`ClaimReductionView` supplies claim flow, reduction contracts, ordered inputs
and outputs, required challenges, publications, and terminal dispositions.
`ExecutionView` supplies the challenge interpretation, visible-history law,
resolver coordinates, generated-execution law, run schema, replay
qualification, and relation-run-view issuance.

This is a semantic read set, not a prescribed serialization. The exact
`PIRStaticViewReadManifest` must be the fixed point of
`RequiredPIRViewReadClosure`; the realized read set must equal it. Thus an
exporter cannot request a dangling check input without its producer/type/order
closure, and cannot read an undeclared extra field without changing the
manifest.

### 4.2 Strategy and honest-prover interpretation

Add `StrategyDecisionView` for decision points, legal moves, visible prefixes,
and guaranteed reads. Add an admitted Plan and `PlanRealizes` result only when
the proposition names a particular honest strategy or witness discipline.
Live private material must remain in owner-local causal views. A portable
formal package may carry role declarations and public commitments, but it may
not turn secret witness values or a causal capability into serialized
authority.

### 4.3 Relation and property interpretation

Add the exact Relation definition/model/instance and correspondence closures
when the proposition mentions statement, witness, satisfaction, extraction, or
relation preservation. Then form a separate Analysis experiment, adversary,
resource, assumption, theorem, or property proposition. Structural Protocol
reification and relation correspondence do not imply the property result.

### 4.4 Dynamic run interpretation

Use a typed `RelationRunView` or other owner-issued dynamic view. Its
qualification is part of the proposition:

- `CausallyGenerated` may support a claim whose premises require restricted
  strategy calls or nonanticipation;
- `ReplayQualified` may support deterministic trace agreement but cannot
  establish causal generation; and
- `Inactive` or `NotReached` is a semantic run fact, not missing data.

`InterpretationFailed`, `StrategyStopped`, deterministic limit exhaustion,
unsupported operation, missing authority, malformed input, and checker failure
remain different outcomes. A formal model that represents all of them as
ordinary rejection is not a correspondence target for the selected Protocol.

### 4.5 Compiler and realization interpretation

For one pass, the source closure additionally names the exact predecessor,
successor, observer/model, relation direction, protected observations,
permitted deltas, lineage maps, and transition proposition. For an endpoint,
it names the exact OIR/target semantics and realization observation. Neither
question should be folded into the Protocol formalization merely to obtain an
end-to-end-looking theorem.

## 5. Candidate reification boundary

The current leading hypothesis separates three values that are easy to
collapse incorrectly:

```text
PortableSemanticReadPackage
  = provider-neutral, exact source coordinates and values

ProviderFormalArtifact
  = VCVio, ArkLib, SSProve, EasyCrypt, or another provider's term/module

FormalCorrespondenceResult
  = Analysis-owned checked relation between the two under one contract
```

These names are placeholders. Their required roles are more important than
their spelling.

### 5.1 Portable semantic read package

The package should contain only:

- exact root owner subject IDs and selected profile IDs;
- the complete canonical authentication preimages and semantic dependency
  closure needed for independent decoders to recompute those IDs, or an exact
  separately specified source-authentication envelope that supplies them;
- exact source-profile and owner-view coordinates;
- exact closed manifests and dependency closure;
- canonical typed source values at every selected coordinate;
- source-to-package coordinate bindings; and
- the exact formal-interpretation contract ID that says which observations
  must be complete and which are intentionally outside the proposition.

It should exclude theorem names, proof-assistant syntax, tactics, proof bytes,
producer identity, source locations, display labels, build logs, and live
capabilities. It is an inert content-addressed value. Its existence grants no
PIR, Relations, Analysis, Compiler, or deployment authority.

The stable package therefore has two logical layers even if one wire envelope
eventually carries both:

```text
source authentication preimages
  + question-relative exact semantic read projection
```

The first lets independent decoders recompute source identities without MLIR.
The second prevents a provider from deriving an undocumented read set from the
full body. Carrying canonical preimages is the cost of the independent-release
trigger; carrying them does not make the package an admitting owner.

Only owner-approved portable static coordinates enter this package. Live
secret witness values, confidential Oracle carriers, mutable Plan state, and
causal capabilities remain in a separate owner-local support lane. A theorem
may quantify over their typed roles or consume an owner-local checked result;
the portable package may not serialize them to claim completeness.

This is deliberately not a universal proof-assistant-independent logic. Each
provider may use its native language and semantics. Provider neutrality lives
in the source package, correspondence proposition, result envelope, and trust
accounting—not in an invented logic that tries to subsume VCVio, SSProve, and
EasyCrypt.

### 5.2 Checked reification

An untrusted exporter may propose a package. A checker must independently:

1. authenticate or re-admit the exact owner subjects under the named regime;
2. recompute every packaged root identity from its complete authentication
   preimage and dependency closure;
3. reissue every owner view and source-authority binding;
4. recompute every required-read fixed point;
5. require exact equality between selected, realized, and packaged reads;
6. reject missing, extra, duplicate, aliased, reordered, or cross-profile
   coordinates;
7. typecheck every packaged value and reference;
8. check the contract's total source-to-package observation map; and
9. return agreements, disagreements, or the exact qualified noncompletion.

The checker result may mint a fresh Analysis capability. Package bytes,
certificate bytes, a Boolean, and a result ID cannot replace that capability.
Cold replay reauthenticates the package, checker/translation contracts,
source/environment bindings, validation basis, and result before minting a new
capability.

### 5.3 Provider correspondence

A second relation checks that one provider artifact interprets the package.
For VCVio this may be an ordered typed oracle computation plus handlers and
trace/probability observations. For ArkLib it may be a partial higher-level IOR
or reduction subject. For SSProve it may be a package/interface composition;
for EasyCrypt, a game/module environment. The relation must be provider-
specific because the semantic observations and trust roots differ.

A provider adapter may refuse an interleaved or shared-challenge subject even
when another provider accepts it. Refusal is evidence that the adapter is
partial, not that the zkc Protocol is malformed.

## 6. Identity and authority rules

The following separation is required for every candidate that survives F0:

| Item | Identity must bind | Authority |
|---|---|---|
| source package | semantic regime/profile IDs, root owner IDs, exact manifests, canonical entries, interpretation-contract ID, package-schema ID | none; inert input |
| provider artifact | source-package ID, provider/environment ID, provider-language/schema ID, complete provider term/module bytes | none; proposed formal object |
| correspondence question | exact source-package and provider-artifact coordinates, observation relation, direction, maps, and required assumptions | proposition meaning only |
| validation basis | checker and ABI, translation contract, decoder/elaborator, finite controls, proof environment, residual trust roots | validation semantics only |
| checked result | exact proposition, basis, support, agreements/disagreements, derivation or certificate, and policy binding | inert record; no live authority |
| affirmative capability | exact checked result, source authorities, consumer, purpose, policy, freshness, and process generation | scoped permission to rely on that result |

Changing theorem provider, checker, package schema, observation relation,
source manifest, profile, or root subject changes the appropriate identity. A
different proof of the same proposition may change derivation and validation
basis without changing the proposition. A refreshed ArkLib pin cannot retain
the old environment identity merely because declaration names still resolve.

## 7. Gap classification

| Gap | Classification | Consequence |
|---|---|---|
| no selected portable source package | independent-consumer/compatibility boundary | F0 must decide the formal-extraction trigger; local owner views alone are insufficient for independently released formal tooling |
| no formal-reification question/result family | Analysis family gap | add a typed family or show an existing generic correspondence family instantiates without semantic ambiguity |
| no package exporter/checker | implementation and evidence gap | F1 should use an untrusted exporter and a smaller checker; exporter success has no authority |
| no provider-artifact correspondence | translation-contract gap | VCVio and ArkLib use separate partial adapters and exact refusal |
| receipt `covers` is authored prose | current implementation gap | retain as provenance, but never upgrade it to checked correspondence by renaming it |
| no property-specific pass relation | Compiler/Analysis instantiation gap | F2 or a later pilot must state one observer and direction; structural target admission is insufficient |
| no dynamic OIR/Realization activation | planned downstream gap | formal Protocol results stop before endpoint claims |

No Core field gap has yet been demonstrated. This is a provisional positive
finding, not proof of completeness. The scenario dossier must still attempt to
erase shared challenge identity, interleaving, Oracle commitment extent,
failure precedence, and causal qualification.

## 8. Provisional W0/W1 conclusion

The strongest current hypothesis is an **A/S/C composition**:

- Candidate A supplies exact owner-derived formal-interpretation source views
  and an Analysis-owned correspondence proposition;
- Candidate S supplies a stable neutral source-read package because an
  independently released formal consumer is the F0 scenario that names the
  documented extraction trigger; and
- Candidate C makes untrusted production plus independent checking the default
  evidence mode for reification and selected transformations, without making a
  certificate mandatory for ordinary Protocol admission.

This W0/W1 result supplied the candidate to beat. The later
[`f0-provisional-architecture-and-entry-contracts.md`](f0-provisional-architecture-and-entry-contracts.md)
provisionally selects it for F1 falsification, not as a durable target
contract. Candidate P remains the
minimum local prototype; Candidate R remains the clean-room formal-center
comparator. F0 reopens the Core or owner split if a scenario shows that the
required fact cannot be expressed through an exact owner view, or that a
question-relative package cannot preserve a theorem-relevant observation
without becoming a shadow Protocol.

## 9. Non-claims

This map does not specify a wire encoding, prove that the source views are
complete, implement a checker, authenticate any external theorem, establish
that VCVio or ArkLib fits a zkc subject, verify the current compiler, or activate
OIR/Realization. It does not make the temporary placeholder names durable.
