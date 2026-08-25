# Analysis transport, composition, and replay

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative target
> **Target status:** Stage 4A durable promotion
> **Provisional owner:** `analysis`
> **Authority:** This document specifies the selected target for `docs-next/`.
> It is non-normative until explicit consolidation and cutover. The current
> specifications under [`docs/`](../../docs/README.md) remain authoritative.
> This document establishes no transported or composed property, replayed
> authority, implementation support, migration feasibility, or consumer
> reliance.

> **K1 transition notice — 2026-08-26:** The identity, algorithm, dependency,
> and replay forms below predate
> [Executable Semantic Foundations](../foundation/executable-foundations.md).
> K3 must reconcile exact source identities and portable or checked bridges
> with K1/K2 before transport or composition can be integrated.

## 1. Scope and governing invariants

This document defines:

- heterogeneous property transport across an exact checked semantic relation;
- property composition over independently admitted children and target;
- exact property-coverage accounting without a universal verified state;
- cold Analysis replay and purpose-bound persistence;
- cache and disclosure boundaries;
- explicit residual-trust closure; and
- the extension law for Analysis families, bases, validators, and operations.

All operations use the exact proposition, basis, outcome, negative-result, and
process-local authority model in the
[Analysis semantic model](analysis-model.md). Direct relation families are in
[Semantic relation families](semantic-relations.md), and cryptographic family
profiles and Fiat--Shamir theorem ports are in
[Cryptographic property families](cryptographic-properties.md).

Every operation below executes through the complete occurrence-local
`AnalysisCheckingInvocation`: exact authenticated request and family policy,
all typed admitted-subject/view and checked-result source bindings, the total
source-policy closure, separately supplied fresh source and checker
capabilities, and the exact named consumer and typed purpose. Signatures may
elide this envelope for readability; no operation may read an ambient value,
policy, binding, or authority.

The governing rules are:

1. Structural construction or correspondence transports no property by
   default.
2. A source judgment can be consumed only at its exact proposition, polarity,
   hypotheses, assurance class, residual trust, `FamilyOperationPolicyId`,
   transitive source-operation-policy dependency closure, and exact judgment-
   record/basis/derivation/support/validation binding.
3. The target is independently admitted; transport or composition never mints
   target admission.
4. Every subject, model, occurrence, witness, relation, observer, and parameter
   map is explicit and checked.
5. Every inherited hypothesis, discharged side condition, and quantitative
   loss is retained in a total ledger.
6. Failure to transport or compose is not a negative target property.
7. Persistence preserves inert reconstruction material, never live authority.
8. Every derived result retains the canonical transitive union of all source-
   owner operation policies; its target policy cannot erase or relax one.

Any transport, composition, coverage, or other derived operation that reads an
owner-local reference or local Analysis/peer-owner handle follows the
[confidential owner-local handle lane](analysis-model.md#confidential-owner-local-handle-lane).
Every concrete value whose own identity preimage names that source or a derived
local handle—normally the instantiated source port, support, derivation,
judgment, coverage, and result—uses its corresponding `Local*Handle` and remains
restricted to the exact same-process named consumer. An independently defined
target question or proposition, and a validation basis whose own preimage is
otherwise public, keeps its portable identity; taint does not flow backward
from private support. Nevertheless, no durable judgment, public digest, cache
entry, replay bundle, or exact cold-replay claim may be created for the local
derivation that establishes that public proposition.

## 2. Heterogeneous property transport

### 2.1 Typed transport signature

Transport may consume a tuple of source propositions from different families
and establish a proposition in a different target family:

~~~text
PropertyTransport<T, SourcePremiseSchemas, PTarget>(
  exact tuple of affirmative established source judgments matching
    SourcePremiseSchemas,
  affirmative
    PropertyTransportPort<T, SourcePremiseSchemas, PTarget>
    or another exact transform-theorem port with the same signature,
  independently admitted target subject,
  exact source-to-target subject, occurrence, relation, witness, observer,
    model, and parameter maps,
  exact side-condition judgment capabilities,
  exact target AnalysisProposition<PTarget>)
  -> AnalysisAttemptOutcome<PTarget>
~~~

`SourcePremiseSchemas` is an ordered typed tuple. Each entry specifies the
source family and regime, proposition schema, required polarity, exact subject
role, accepted hypothesis form, and quantitative sort. Reordering, dropping,
or duplicating a premise creates a different port or malformed invocation.
Accepted assurance classes, residual-trust closures, and source capability
operation policies belong to concrete support qualification and the target
operation policy; they are not part of the semantic transport proposition.

The port fixes:

- theorem or transform-rule identity and direction;
- the exact source theorem/transform proposition, hypothesis context,
  `JudgmentRecordId`, `BasisQualificationId`, assurance class, residual-trust
  closure, `FamilyOperationPolicyId`, transitive source-operation-policy
  dependency closure, exact named consumer, typed `OperationPurpose`, complete
  `ExactCheckedResultAuthorityBinding` and inert `OwnerCapabilityRequirement`,
  and exact derivation/support/semantic/validation binding under which its live
  capability was minted;
- exact source proposition schemas and target family/regime;
- subject, model, occurrence, relation, witness, observer, and parameter map
  schemas;
- extra hypothesis and side-condition schemas;
- one exact typed quantitative transformer.

A port is attenuated process-local authority. Attenuation preserves the exact
source proposition, hypotheses, judgment record, basis qualification,
derivation, support, semantic and validation bases, assurance, residual trust,
`FamilyOperationPolicyId`, and transitive source-operation-policy dependency
closure, named consumer, typed `OperationPurpose`, and complete checked-result
source binding. Its ID or replay bytes cannot replace the live
theorem-instance or transform-theorem capability from which it was minted.

### 2.2 Target reconstruction

The checker independently recomputes the exact target conclusion. It requires
the target proposition's hypothesis context to equal:

~~~text
canonical union(
  every inherited source hypothesis,
  theorem and checked-relation hypotheses,
  every undischargeable side condition)
minus only hypotheses discharged by exact checked rules
~~~

The derivation retains a total substitution and quantitative-loss ledger. For
its uninterrupted authority lifetime, the completed live transport-derivation
occurrence retains every exact matching source-judgment, theorem, relation, and
side-condition capability used decisively. Its durable derivation record retains
the exact portable `ExactCheckedResultAuthorityBinding` values through its exact
support instantiation, including each complete result coordinate, origin,
qualified facts, assurance/trust, policy disposition and closure, and inert
`OwnerCapabilityRequirement`, together with subject/model/occurrence maps,
semantic and validation bases, and residual-trust roots. It exists only in the
untainted portable lane. No live capability
enters a durable record or content identity. A completed target capability is
minted only when the target policy and every source-owner policy permit this
exact derivation purpose, and it retains their complete canonical closure.

Hypothesis equality is structural under the canonical typed DAG. The checker
cannot infer logical equivalence, drop a stronger restriction, weaken a bound,
or replace an assumed correspondence with an established one without an exact
rule and support.

### 2.3 Heterogeneous and same-family cases

A transport may, for example, consume an exact restricted
state-restoration-soundness proposition and exact side conditions to establish
a distinct plain-soundness target proposition. It does not cast one family to
another. The port and rule state the exact implication.

The same discipline applies when source and target families share a name.
Changing the property regime, model, observer, occurrence, bound, or
quantitative transformer requires a different port. Equality of Protocol IDs
does not permit an unqualified property cast.

Direct target analysis remains independent. It may establish the same
`AnalysisPropositionId` through another basis, but its assurance and trust are
not merged with the transported derivation.

### 2.4 Qualified failure

Transport returns:

- `Completed(Affirmative)` only after exact target reconstruction and checking;
- a family-negative target only when an independent exact refutation basis
  establishes the counter-proposition;
- `Unsupported` for a missing family, rule, port, or semantic regime;
- `CannotAnswer` for missing exact premises, correspondences, maps, or side
  conditions;
- `Refused` for absent live authority or prohibited disclosure;
- `Malformed` for a type, identity, polarity, cycle, or framing error; or
- `CheckerFailure` for operational failure with no semantic conclusion.

A failed source premise, inapplicable theorem, wrong port, or unsuccessful
transport never produces a negative target property.

## 3. Property composition

### 3.1 Inputs and ownership

Property composition starts only after PIR has independently admitted every
child and target, admitted the exact composition specification, and minted an
affirmative `CheckedCoreComposition` with resolved maps. The structural result
does not establish a property.

~~~text
PropertyComposition<P, Op>(
  exact affirmative child occurrence judgment capabilities,
  independently admitted target,
  admitted composition specification,
  affirmative CheckedCoreComposition with resolved maps,
  exact operator and property theorem,
  exact randomness and challenge topology,
  exact relation and witness morphisms,
  exact captured failures and reaches,
  exact terminal and suppression policy,
  admitted ChangeContracts and affirmative ChangeConforms capabilities,
  exact side-condition judgment capabilities,
  exact assumptions, substitutions, and quantitative-loss ledger,
  exact target AnalysisProposition<P>)
  -> AnalysisAttemptOutcome<P>
~~~

Analysis owns the property theorem and target derivation. PIR owns child,
target, and composition admission and the structural composition result.
Relations owns relation semantics, satisfaction, and correspondence. No owner
may be bypassed by embedding its conclusion in an Analysis rule.

### 3.2 Operator-specific laws

The v0 operator vocabulary may include:

~~~text
Sequential
Parallel
Interleaved
Concurrent
SharedChallenge
Batched
Repeated
Lift
FailureCapture
FiatShamirTransform
~~~

Each operator profile closes its state combination, scheduling, occurrence
maps, randomness and challenge sharing, relation/witness morphisms, failure
capture, reachability, terminal suppression, abort, and quantitative laws. A
property family exposes only the composition rules justified for that exact
operator and model.

Child property truth alone is never a composition theorem. A sequential rule
does not apply to interleaving; independent-challenge reasoning does not apply
to shared challenges; single-session reasoning does not apply to concurrency;
and captured failure changes require admitted declarations and exact
`ChangeConforms` results.

### 3.3 Hypotheses, losses, and occurrences

Every child judgment is bound to one exact child occurrence, even when two
occurrences share a `ProtocolId`. Child residual hypotheses are inherited
exactly. A theorem may discharge only its declared side conditions. It may add
new scheduling, independence, termination, state-separation, or relation-
morphism hypotheses.

The quantitative ledger records each child bound, substitution, union or
product law, conditioning event, abort/failure mass, and output expression.
Dimensionally invalid or unsupported expressions are `Malformed` or
`Unsupported`, never approximated silently.

Failure to compose yields a qualified nonsemantic outcome. A negative target
property requires its own family-owned refutation basis.

## 4. Property coverage and reliance

### 4.1 Four separate owners

Coverage separates four responsibilities:

1. PIR, Relations, or another structural owner exports the exact finite claim,
   round, occurrence, observer, or obligation surface.
2. The Analysis family profile expands that surface into exact proposition
   obligations when expansion is part of property meaning.
3. Analysis checks exact proposition, polarity, subject, map, model,
   hypothesis, bound, assurance, operation policy, and trust matches and
   returns a factored ledger.
4. The named relying consumer defines which obligations and qualifications
   are sufficient for its use.

Analysis cannot invent the structural surface or the consumer's reliance
policy.

### 4.2 Requirement manifest and check

~~~text
AnalysisRequirementManifest {
  owner_and_purpose,
  exact_source_surface_and_expansion_profile,
  exact_required_proposition_patterns_and_polarities,
  exact_accepted_hypothesis_and_bound_predicates,
  exact_accepted_assurance_operation_policy_and_trust_root_predicates
}

CheckAnalysisCoverage(
  admitted owner-defined AnalysisRequirementManifest,
  exact source-owned surface views,
  exact qualified Analysis judgment capabilities,
  exact occurrence and projection maps,
  admitted Analysis coverage family profile,
  exact target AnalysisProposition<AnalysisCoverage>)
  -> AnalysisAttemptOutcome<AnalysisCoverage>
~~~

`AnalysisCoverage` is an ordinary closed Analysis family, not a parallel
qualification or capability system. Its question binds the exact admitted
manifest and source-surface fact closure, occurrence and projection maps, and
coverage semantic profile. The manifest, every source-owned view, and every
input judgment enter the complete `AnalysisCheckingInvocation` with their exact
source bindings and separately supplied fresh capabilities. Its completed live
authority is the common `EstablishedAnalysisJudgment`, including the exact
judgment and checked-result authority bindings; the portable completed record
may be named `CheckedAnalysisCoverage`, but that record is inert.

An affirmative result means only that the supplied exact judgments cover the
exact manifest. A family negative is available only when the admitted coverage
profile defines a complete decision relation and the checker establishes the
exact counter-proposition; it retains every missing, wrong-subject, wrong-map,
wrong-model, wrong-polarity, wrong-hypothesis, wrong-bound, wrong-assurance,
wrong-operation-policy, or wrong-trust entry. Missing authority or unavailable
inputs instead produce the corresponding common nonsemantic outcome. This is a
coverage result, not a negative cryptographic property.

Coverage does not imply truth beyond the supplied proposition capabilities,
acceptance of their hypotheses or trust by another consumer, Protocol
admission, endpoint realization coverage, or a universal
`ArtifactVerified`/“all claims” state.

## 5. Cold Analysis replay

### 5.1 When persistence exists

An `AnalysisReplayBundle` exists only for a named independent consumer,
expensive reconstruction, or a real cross-process trust separation. Cheap
direct checks are recomputed by default. Creating a bundle merely for logging
or convenience is not a new semantic need. A result whose support contains an
owner-private nonserializable premise-record reference is process-local and has
no exact cold-replay bundle; a later confidential rerun creates a new support,
derivation, and result local-handle chain.

Bundle creation is refused unless every immediate and transitive source has one
freshly authenticated owner-policy disposition. Every `BoundTo` policy must,
together with the target policy, permit creation, retention, disclosure, lookup,
and replay for the exact named consumer and purpose; every
`OwnerDefinesNoOperationPolicy` disposition must be backed by its exact admitted
owner capability-contract and ABI preimage. It is
also refused when exact owner-authorized reconstruction material or explicit
external owner replay prerequisites for any decisive premise or
correspondence-support result cannot be retained.

The bundle retains:

- the complete canonical typed ledger of every portable input
  `ExactAdmittedSubjectAuthorityBinding` and
  `ExactCheckedResultAuthorityBinding`, including each inert
  `OwnerCapabilityRequirement`; an owner-local coordinate makes the dependent
  replay bundle unavailable;
- exact subject reconstruction manifests and semantic regimes;
- semantic and basis read closures and source-owned view reconstruction rules;
- exact model, question, proposition, and hypothesis closure;
- the exact operational request, its complete
  `PreExecutionRequestRealizationLedger<F>`, and its exact
  `CompletedRequestRealizationLedger<F>`, including the initial exact-
  proposition binding or derive-within schema reservation, the completed
  proposition and admission binding, target-realization result, achieved
  assurance acceptance, and terminal resource accounting;
- the exact authenticated target `FamilyOperationPolicy` and every transitive
  source-owner policy disposition: either the complete operation-policy preimage
  or the exact owner capability-contract and ABI preimage that explicitly
  declares no separate policy, plus the corresponding admission manifests,
  exact IDs/coordinates, and the complete source-policy dependency closure governing request,
  capability, use, disclosure, trust, persistence, and replay behavior;
- exact canonical preimages, admitted IDs, and admission manifests for every
  `FamilySemanticProfile`, `FamilyBasisRegistry`, and
  `FamilyValidationProfile` read by the question or selected bases;
- semantic basis, support requirements, and validation basis;
- exact owner-authorized reconstruction material, or exact external owner
  replay prerequisites and acquisition contracts, for every decisive premise
  and correspondence-support record; no inert owner record is treated as
  authority;
- proof, certificate, refutation, or direct-check material;
- exact theorem, model, statement, and occurrence-correspondence propositions;
- checker contracts and implementation/dependency identities;
- expected qualified result, assurance, residual trust, and the complete output
  `ExactCheckedResultAuthorityBinding<Analysis, F>`, including its result
  coordinate, complete origin and completed-outcome facts, policy closure,
  named consumer, typed purpose, and inert `OwnerCapabilityRequirement`;
- named consumer and replay purpose; and
- exact disclosure and confidential-material policy.

### 5.2 Replay and occurrence identities

~~~text
AnalysisReplayBundleId = H(
  "zkc/analysis-replay-bundle",
  exact canonical AnalysisReplayBundle,
  named consumer identity,
  exact replay purpose and disclosure policy)

ReplayOccurrenceHandle =
  fresh process-local nonserializable owner-issued handle

AuditEventRecordId = H(
  "zkc/analysis-replay-audit-event",
  AnalysisReplayBundleId,
  owner-issued inert occurrence reference,
  exact record-relative operation and outcome classification)
~~~

`ReplayOccurrenceHandle` is deliberately not a content ID and cannot cross
reset or serialization. `AuditEventRecordId` may distinguish inert audit
statements associated with repeated attempts, but checking the record
authenticates only its bounded record content. Neither it nor its owner-issued
reference proves that an occurrence, operation, or outcome happened or mints
Analysis authority. Such a historical claim requires a separately owner-
authenticated occurrence/log result, which Stage 4A does not define.

The replay bundle identifies stable reconstruction content. The occurrence
handle identifies one live local execution. The audit record identifies one
inert record-relative accounting statement. Collapsing the three would either
make content identity nondeterministic or let stored bytes impersonate
authority.

### 5.3 Cold replay algorithm

Cold replay:

1. reconstructs every recorded admitted-subject binding, authenticates and
   re-admits every subject, reacquires the fresh capability separately, and
   requires complete binding equality and total no-missing/no-extra association
   of every admitted semantic subject and model instance to the exact question
   subject/model and semantic-read closures;
2. recreates every source-owned view, obtains fresh owner-minted purpose-
   specific view/admission capabilities separately, and requires complete
   equality with each recorded source binding, including view contract, read
   manifest, subject, consumer, purpose, and `OwnerCapabilityRequirement`, plus
   semantic and basis adequacy; view-shaped records alone are refused;
3. reconstructs, authenticates, and re-admits every exact family semantic
   profile, basis registry, and validation profile, obtains their fresh admitted
   capabilities, and checks their IDs and used slices against the question and
   bases;
4. authenticates and re-admits the exact target family operation policy and
   every source-owner policy disposition; `BoundTo` reconstructs the complete
   policy preimage and fresh policy/purpose authority, while
   `OwnerDefinesNoOperationPolicy` reconstructs the exact owner capability-
   contract and ABI preimage plus fresh owner contract admission or mediated
   confirmation; it checks exact equality to the recorded transitive closure and
   requires every bound policy to permit this named replay consumer and purpose;
5. authenticates and re-admits the exact question and, only for an
   `ExactProposition` target, the requested proposition, then obtains their
   fresh family-owned admitted capabilities; a `DeriveWithin` target instead
   retains only its exact result-schema reservation and has no initial
   proposition capability. It authenticates every other category through its
   required lifecycle, including hypotheses, semantic basis,
   support-instantiation requirements, and validation basis, then obtains fresh
   matching premise and correspondence capabilities only by executing their
   retained owner-authorized reconstruction material or exact external owner
   replay prerequisites. It reconstructs each checked-result source binding,
   requires complete equality against the separately reacquired capability,
   reconstructs the complete `PreExecutionRequestRealizationLedger<F>`, and
   requires exact equality with the recorded ledger; ambient lookup and
   authority-by-record are forbidden;
6. obtains a fresh checker-execution capability and checks its implementation
   identity, ABI, contract, and implementation-to-contract correspondence set
   against the exact validation basis;
7. rechecks external proof, statement/model/subject correspondence,
   certificate translation, or direct procedure as applicable;
8. reruns the derivation through the exact validation basis; for a
   `DeriveWithin` target it then authenticates and admits the produced
   proposition, obtains the exact admitted-subject binding and separately fresh
   matching capability, and checks the identical question and reserved result
   schema; for `ExactProposition` it checks exact target equality;
9. seals the complete `CompletedRequestRealizationLedger<F>` from that exact
   pre-execution ledger, completed proposition and admission binding,
   target-realization result, achieved-assurance acceptance, and total terminal
   accounting, then requires complete equality with the recorded completed
   ledger before accepting any completed outcome;
10. requires exact proposition, outcome, assurance, retained facts, residual
   trust, `DerivationId`, `SupportInstantiationId`, `SemanticBasisId`,
   `ValidationBasisId`, `FamilyOperationPolicyId`, and final `JudgmentRecordId`
   equality with the expected exact record, then recreates the complete final
   `ExactCheckedResultAuthorityBinding<Analysis, F>`, including its result
   coordinate, complete origin, completed-outcome and request-realization facts,
   policy closure, named consumer, typed purpose, and inert
   `OwnerCapabilityRequirement`, and requires exact equality with the bundle's
   expected output binding; and
11. mints a fresh process-local capability only under the exact target policy
    and fully revalidated source-policy disposition closure after successful
    completion.

Replay never accepts prior exit codes, signatures, stored judgment records,
matching IDs, or cached capabilities as authority. A replay using a changed
basis may establish the same proposition under a new qualification, but it is
not replay of the old exact result.

## 6. Persistence and disclosure

### 6.1 Inert durable records

Question, proposition, basis, derivation, judgment, coverage, and replay
records may be persisted only when the exact target family operation policy and
every policy in the transitive source-operation-policy dependency closure permit
creation, retention, disclosure, and lookup for this named consumer and
purpose. Every operation, judgment, replay, and audit record binds the target
`FamilyOperationPolicyId` and exact source-policy closure. A durable record is inert. It supports
audit, comparison, and later reconstruction; it does not preserve admitted
subjects, result capabilities, checker processes, or authority-bearing views.

After serialization, FFI, mutation, process reset, or dependency change, every
live capability is gone. Equal IDs locate exact material but do not skip
authentication, admission, or checking.

### 6.2 Confidential material

Secret witnesses, adversarial private state, simulator trapdoors, extractor
state, private oracle state, sensitive traces, and confidential counterexamples
are excluded from public bundles. A family may:

- prohibit persistence;
- persist only a redacted public record;
- require a separately owned confidential replay store and access policy; or
- persist a non-revealing proof/certificate whose semantic and validation
  contracts are independently specified.

An owner-private premise-record reference and every value whose own identity
preimage directly or through a local child contains it are likewise excluded
from public bundles, records, and caches. Those affected supports, derivations,
judgments, coverage results, attempts, results, and any actually dependent
semantic or validation values use owner-local handles and may be disclosed only
to the exact same-process consumer authorized by the conjunction of all source-
owner and target operation policies. An independently public question,
proposition, rule schema, semantic basis, or validation basis keeps its portable
identity when its own preimage contains no local child, but a local derivation
of it still has no durable judgment or exact cold replay.

A digest of secret material is not a safe default: it may create a global
equality oracle. Occurrence-local private capability identity remains separate
from public content identity.

## 7. Cache taxonomy

The target distinguishes:

~~~text
ProofSearchCache
  unauthoritative tactics, intermediate lemmas, solver hints, and discovery

SemanticReplayCache
  immutable basis, proof, certificate, and reconstruction material that still
  requires exact revalidation

EvidenceInputCache
  exact attributable Evidence records or policy-qualified appraisals retaining
  producer observation meaning, environment, procedure, time, and uncertainty

ProcessLocalAuthorityMemo
  owner-internal reuse of an already live capability under identical immutable
  dependencies and within one uninterrupted authority lifetime
~~~

A persistent cache key includes every semantic subject, regime, question,
proposition, model, hypothesis, semantic and validation basis, support
requirement, checker contract, correspondence, exact family operation policy,
exact transitive source-operation-policy dependency closure, every bound source
policy identity and authenticated contract, exact named consumer and purpose,
every completed source judgment or result binding with its record or local
reference and exact derivation, support, semantic-basis, and validation-basis
coordinates, environment, disclosure, and version coordinate that may affect
the cached material. A persistent key exists only in the fully portable lane;
any local handle makes persistent caching unavailable. A hit is only a hint
until exact key reconstruction and owner revalidation complete.

Basis or dependency drift makes an entry stale. It does not make the semantic
proposition false. Matching digests, signed cache entries, previous decision
IDs, or old success records cannot rehydrate a live capability.
`ProcessLocalAuthorityMemo` may reuse authority only while the capability has
never crossed serialization, reset, process, authority lifetime, or dependency
identity.

## 8. Residual trust

### 8.1 Exact rooted closure

Every completed result carries a finite acyclic `ResidualTrustClosure`. Each
node states one exact correctness or adequacy proposition, and each edge states
why it depends on another. Every path terminates at an explicitly identified
root. `trusted`, `machine checked`, `zkc`, a project name, or an institution
name is not a root.

Representative root forms are:

~~~text
NormativeSemanticDefinitionRoot(
  exact regime, model, or rule identity and exact adequacy claim)

SourceAdmissionRoot(
  exact owner operation and checker contract)

CheckerImplementationRoot(
  exact implementation identity,
  exact contract-correspondence claim,
  exact execution-platform identity)

ExternalKernelRoot(
  exact logic, kernel, elaborator, imports, and soundness claim)

CertificateDecoderOrTranslationRoot(
  exact language, decoder or translation, and adequacy claim)

TrustedDecisionOracleRoot(
  exact engine, input contract, and asserted claim)

MeasurementProcedureRoot(
  exact environment, procedure, and uncertainty claim)
~~~

`ResidualTrustClosureId` hashes the complete rooted DAG, including every exact
root claim and identity. Missing, cyclic, generic `other`, or free-text roots
make the basis malformed or unsupported.

### 8.2 What remains visible

Every completed record names, rather than hides:

- semantic-regime and model adequacy;
- rule or theorem truth and faithful encoding;
- subject-to-model and external-statement correspondence;
- checker implementation correctness or formal-verification boundary;
- certificate decoding, translation, and proof-checker assumptions;
- admitted dependency meanings; and
- measurement environment, procedure, and uncertainty when applicable.

A formally verified checker replaces an implementation root only with its
exact proof-kernel, formal model, compiler, extraction, and execution roots. It
does not erase the trust base. “Small checker,” “verified producer,” “machine
checked,” “certificate accepted,” and “replayed” are distinct qualifications.

### 8.3 Hypotheses are not trust roots

A hardness assumption, unproved external theorem, assumed model
correspondence, or termination assumption belongs to the proposition's
`AnalysisHypothesisContext`. A checker, encoding, kernel, runtime, or
definition-correctness obligation belongs to residual trust. A consumer may
accept or reject either, but cannot move an item between categories to preserve
an identity or assurance label.

Transport, composition, and coverage carry the exact union of every trust root
used decisively. They cannot retain only the roots of the final proposition
and omit those used for source judgments, theorem ports, correspondence,
side-condition discharge, quantitative transformation, or coverage matching.

## 9. Extension law

### 9.1 Open operational implementations

The following may change without redefining proposition meaning:

- a proof producer or search tactic for an existing semantic-basis contract;
- a solver strategy that emits the same admitted certificate language;
- a checker implementation independently authenticated against an unchanged
  exact validation contract, producing a new `ValidationBasisId` and trust
  closure;
- a new derivation, proof, theorem instance, or certificate accepted under an
  existing family, basis registry, theorem schema, correspondence adapter, and
  proof-rule set; and
- cache, scheduling, or parallelization strategy that affects no semantic
  input.

These changes may alter request, validation, derivation, qualification, trust,
or replay identities. They do not alter `AnalysisQuestionId` or
`AnalysisPropositionId` unless proposition meaning also changes.

### 9.2 Reviewed profile extensions

A reviewed change to the appropriate semantic, basis, validation, or operation
profile is required for a new or changed:

- Analysis family, subject grammar, model, experiment, observer, occurrence,
  conclusion, or refutation meaning;
- semantic read requirement or quantitative algebra;
- theorem/rule schema or external semantic-correspondence adapter;
- certificate semantic language, proof-rule set, or checker contract/ABI;
- implication, transport, composition, or coverage port schema;
- qualified outcome, negative semantics, capability policy, or assurance
  meaning; or
- persistence, replay-consumer, disclosure, or residual-trust contract.

Every family closes its `FamilySemanticProfile`, `FamilyBasisRegistry`,
`FamilyValidationProfile`, and `FamilyOperationPolicy` independently. A change
to subjects, occurrences, maps, semantic reads, model, experiment, observer,
quantitative meaning, conclusion, or refutation changes
`AnalysisSemanticRegimeId` or `FamilySemanticProfileId`. A new theorem, rule,
proof lane, checker, capability policy, replay consumer, or trust policy
changes only the basis, validation, operation, or replay identity that reads it
unless proposition meaning also changes.

Unknown semantic tags are `Unsupported`. Dynamic callbacks and registration
cannot create a family, model, rule, negative meaning, or capability cast.
Cross-version reuse requires an exact checked interpretation or transport
proposition. Existing identities are never reinterpreted.

## 10. Selected nonclaims

This specification does not establish:

- any transported, composed, or covered property;
- correctness of a transport theorem, composition theorem, coverage profile,
  replay procedure, cache key, trust root, checker, or correspondence;
- a target property from source-property truth and structural adjacency alone;
- a negative target property from failed transport or composition;
- consumer acceptance from an affirmative coverage result;
- a global verified state, endpoint feasibility, release readiness, or
  implementation correctness;
- confidentiality merely because a public record omits secret bytes;
- authority from persisted records, replay bundles, audit events, cache hits,
  signatures, or matching IDs; or
- implementation support, migration feasibility, or safe deployment of any
  extension.
