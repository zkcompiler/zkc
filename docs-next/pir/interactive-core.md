# Interactive Core and Causal Execution

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative K2 target with K3-B consumer view
> **Target status:** K2 identity-bearing Core and execution body complete;
> K3-B execution-issued relation grounding view, bounded K3-C Analysis
> consumption, bounded K3-D endpoint projection, and finite K3-E executable
> integration evidence recorded; owner profile preimages remain open, K4 is
> next, and K5 freeze remains pending
> **Provisional owner:** `pir`
> **Authority:** None during the transition. Current normative Protocol
> semantics remain under [`docs/`](../../docs/README.md).

## 1. Contract

This page is the sole K2 definition owner for:

- the finite verifier-observable `InteractiveCore`;
- its identity, formation, admission, and structural source views;
- public instance bindings and explicit composition scopes;
- its base effects and standard immutable-oracle extension;
- typed claims, reductions, checks, and terminal closure;
- legal actor-visible histories and prover decisions;
- causal strategy-generated execution and non-authoritative replay; and
- structural public-coin eligibility; and
- the execution-issued, occurrence-scoped view used by Relations grounding.

The companion [Fiat--Shamir Construction](fiat-shamir.md) owns transcript
state, derived required influence, challenge sampling, and the checked Fresh/FS
relation. Foundation owns the identities, values, algorithms, typed failures,
evaluation contracts, and operational outcome distinctions reused here.

PIR does not own witness satisfaction, adversary classes, soundness, knowledge,
zero knowledge, theorem applicability, concrete suppliers, proof serialization,
endpoint projection, or implementation evidence.

## 2. Foundation notation and limits

K2 uses the definitions in
[Executable Semantic Foundations](../foundation/executable-foundations.md)
without aliases that can change their meaning:

- `PriorMetaAuthenticationBasis B`;
- `SemanticContentId<K>(B, body)` and `ContentRefV0`;
- `SemanticModuleId` and authenticated exact-used module closure;
- `ValueType` and `CanonicalValue<T>`;
- `PortableAlgorithmRef`, its derived `SemanticFunctionType`, and admitted
  `EvaluationContractId`; and
- completed `Success`/typed `DomainFailure` versus `Unsupported`,
  `MissingDependency`, `KindMismatch`, `Malformed`, `Refused`,
  `DeterministicLimitExceeded`, and `CheckerFailure`.

Every sequence on this page is finite and ordered. A set is encoded as the
sorted-unique sequence under the exact canonical body bytes of its elements.
Every local reference is an unsigned dense ordinal into the named sequence.
`None | Some(x)` is a K1 finite variant, never a null value. Naturals and all
aggregate bodies fit the constitutional K1 limits. Additionally:

```text
maximum Core occurrences             = 2^14
maximum values, inputs, scopes,
  challenges, oracles, checks,
  claims, reductions, and terminals  = 2^14 each
maximum entries declared by one Oracle = 2^14
maximum direct occurrence inputs     = 2^14
maximum scope depth                  = 384
```

These local ceilings do not relax the smaller cumulative K1 byte, node, edge,
or depth bound. Formation preflights the enclosing canonical body before
materializing a derived aggregate. Reaching a limit is allowed; crossing it
produces no Core ID.

The shared K1 semantic regime supplies only the common identity, value, and
evaluation mechanisms. PIR-specific meaning is selected by the exact
owner-local language profile and, where a body directly cites extensible
meaning, its exact-used same-regime semantic modules. All of them use the exact
`B.semantic_regime.id` in the authenticated `PriorMetaAuthenticationBasis B`;
there is no second PIR or transcript-construction regime axis. A Core, either
Protocol interpretation, and any transcript construction for that Core use the
same complete `B`, including its identity profile, hash suite, semantic-regime
descriptor, and semantic-regime ID. Equality of a bare digest or only one
component is insufficient. A Core may import additional same-regime semantic
modules under Section 8, but only exact-used imports enter its body.

Several Core fields need nominal semantic coordinates without asking PIR to
prove the theorem or cryptographic meaning attached to them. K2 uses one
closed reference form for that purpose:

```text
ProtocolDeclarationRef<K> = ModuleDeclarationRef<K>

For x = (m, K, n):
  ModuleDeclarationRefBody(x) =
    DeclarationRefBody(Module(m, K, n))
  ModuleOwner(x) = m

SemanticModuleRefBody(m) = MetaBytes(ContentRefV0(m))

NominalProtocolDeclarationBody = MetaRecord {
  0: MetaSymbol(nonempty semantic symbol)
}
```

The exact-used PIR owner-module closure recognizes this body for the
declaration kinds
`"pir.message-channel"`, `"pir.challenge-domain"`,
`"pir.public-coin-law"`, `"pir.coin-correlation-group"`,
`"pir.challenge-sharing-contract"`, `"pir.claim-contract"`,
`"pir.reduction-contract"`, and `"pir.oracle-binding-contract"`.
`ModuleDeclarationRefBody` is the mandatory Foundation union injection: a bare
`ModuleDeclarationRef` is never passed directly to `DeclarationRefBody` and a
module ID is never encoded as an untyped digest. The reference is an
authenticated, owner-qualified nominal coordinate. It is not resolved by its
symbol, and its formation alone proves no distribution, claim denotation,
reduction theorem, or binding property. Section 8 derives the exact direct
owner-module set; later Analysis reads the exact reference when assigning such
meaning.

## 3. Subjects and identities

### 3.1 Exact PIR language-profile split

K2 does not place one catch-all PIR language above every subject. It selects
three standalone K1 `SemanticLanguageProfile` owners and the following exact
import topology. This display is a symbolic owner schema, not publication of
the complete six-field K1 profile preimages or their full typed IDs:

```text
PIRInteractionProfile = {
  profile_imports: {},
  supported_subject_kinds:
    {"pir.interactive-core", "pir.protocol", "pir.invocation",
     "pir.source-binding-payload", "pir.source-capability-requirement",
     "pir.source-consumer", "pir.source-no-policy",
     "pir.source-policy-closure", "pir.source-purpose"},
  declarations:
    {InteractiveCoreBody, FreshProtocolBody, CoreInvocationBody,
     CoreStaticViewSchemas, ProtocolExecutionViewSchema}
}

PIRTranscriptFSProfile =
  the companion page's profile importing exactly PIRInteractionProfile

PIRPublicSetupProfile = {
  profile_imports:
    {PIRInteractionProfileId, PIRTranscriptFSProfileId},
  supported_subject_kinds:
    {"pir.public-setup-invocation-view",
     "pir.source-binding-payload", "pir.source-capability-requirement",
     "pir.source-consumer", "pir.source-no-policy",
     "pir.source-policy-closure", "pir.source-purpose"},
  declarations:
    {PublicSetupInvocationViewBody, its projection and issuance laws}
}
```

The required authenticated import closure is selected-root-specific once each
owner has published its complete profile preimage:

```text
ExactProfilePreimages(PIRInteractionProfileId) =
  {PIRInteractionProfileId}
ExactProfilePreimages(PIRTranscriptFSProfileId) =
  {PIRInteractionProfileId, PIRTranscriptFSProfileId}
ExactProfilePreimages(PIRPublicSetupProfileId) =
  {PIRInteractionProfileId, PIRTranscriptFSProfileId,
   PIRPublicSetupProfileId}
```

These are exact no-extra closures. The three-entry convenience bundle is not a
valid Interaction or Transcript/FS intake. Profile imports are ordinary
profile edges, not module roots. The combined public-view profile imports both
Protocol languages because one public-setup view family may name either a
Fresh or an FS `ProtocolId`; changing an unrelated profile outside this
three-node cone does not rotate these subjects.

The bounded executable witnesses instantiate deterministic finite profile
bodies to test this topology, authentication, and rotation behavior. Those
pins are evidence, not PIR semantic authority. The owning PIR pages still have
to publish every complete owner-local `SemanticLanguageProfileBody`--including
the exact family, revision, imports, supported kinds, declaration catalogs,
and semantic-law-source bytes--and its independently reconstructible full
typed ID before any dependent K4 ID is treated as persistent and before K5
freeze.

Every formation, authentication, admission, view-issuance, and view-validation
operation selects exactly one root profile, authenticates only that root's
exact closure, requires that exact root ID in the evaluator's supported-profile
set, and checks every identified subject it forms against the root's
`supported_subject_kinds`. Lack of evaluator support is `Unsupported`; a
supported profile that omits a required subject kind is `Refused`; malformed
profile or closure structure is `Malformed`. Thus an Interaction-only
evaluator may issue Core and Fresh views without supporting Transcript/FS or
public-setup semantics, while those downstream operations remain
`Unsupported`; support never flows backward.

Every identified subject below uses K1 `ProfiledSemanticId`, so the directly
selected profile ID is in the subject preimage. The `"pir.protocol"` subject
kind is deliberately supported by two profiles: Fresh selects
`PIRInteractionProfileId`, while Fiat--Shamir selects
`PIRTranscriptFSProfileId`. The profile ID makes those meanings unambiguous.

### 3.2 Core and Protocol

```text
InteractiveCore = {
  used_modules: CanonicalSortedUniqueSeq<SemanticModuleId>,
  public_inputs: CanonicalSeq<PublicInputDecl>,
  verifier_private_inputs: CanonicalSeq<VerifierPrivateInputDecl>,
  constants: CanonicalSeq<TypedConstantDecl>,
  derived_values: CanonicalSeq<DerivedValueDecl>,
  scopes: NonEmptyCanonicalSeq<ScopeDecl>,
  bindings: CanonicalSeq<PublicBindingDecl>,
  challenges: CanonicalSeq<ChallengeDecl>,
  oracles: CanonicalSeq<OracleDecl>,
  checks: CanonicalSeq<CheckDecl>,
  claims: CanonicalSeq<ClaimDecl>,
  reductions: CanonicalSeq<ReductionDecl>,
  terminals: NonEmptyCanonicalSeq<TerminalDecl>,
  occurrences: NonEmptyCanonicalSeq<OccurrenceDecl>
}
```

The identity-bearing body is `InteractiveCoreBody` in Appendix A:

```text
CoreId = ProfiledSemanticId<"pir.interactive-core">(
  B, PIRInteractionProfileId, InteractiveCoreBody(core))
```

Display names, source locations, MLIR syntax, authoring labels, diagnostics,
plans, suppliers, compiler routes, research notes, and evidence are absent from
the body.

One admitted Core may have two challenge interpretations:

```text
ChallengeInterpretation =
    Fresh
  | FiatShamir(TranscriptConstructionId)

Protocol = {
  core_id: CoreId,
  challenge_interpretation: ChallengeInterpretation
}

ProtocolLanguageProfile(Fresh) = PIRInteractionProfileId
ProtocolLanguageProfile(FiatShamir(_)) = PIRTranscriptFSProfileId

ProtocolId = ProfiledSemanticId<"pir.protocol">(
  B, ProtocolLanguageProfile(protocol.challenge_interpretation),
  ProtocolBody(protocol))
```

`TranscriptConstructionId` is defined by the companion page. `Fresh` is one
closed tag; its challenge laws are already in the Core. The two Protocol IDs
are distinct while retaining one literal `CoreId`.

### 3.3 Lifecycle

```text
CanonicalCoreCandidate
  --AuthenticateCore--> AuthenticatedCoreCandidate
  --AdmitCore---------> AdmittedCore

(AdmittedCore, Fresh)
  --AdmitFresh--------> AdmittedFreshProtocol

(AdmittedCore, admitted TranscriptConstruction)
  --AdmitFS-----------> AdmittedFSProtocol
```

Authentication recomputes the typed Core ID and every consulted K1 dependency
inside one request-local hash-binding ledger. It grants no semantic authority.
Admission runs the closed predicates in Section 10. Only an immutable exact
`AdmittedCore` may be used for execution or a checked construction.

An admitted handle retains the exact ID, canonical body, authenticated prior-
meta basis, exact-used module and algorithm closure, admission regime, and
evaluator identity. Serialization is not the handle.
`AdmitFresh` retains the supplied Core handle's evaluator identity. Any cold
consumer first reauthenticates and readmits serialized subjects through its own
evaluator; an ID or record never transfers another evaluator's admission
authority.

## 4. Parties, inputs, values, and scopes

### 4.1 Parties and external sources

The base v0 Core has exactly two protocol parties:

```text
Party = Prover | Verifier
```

Public invocation values and public coins are typed external sources, not a
third party. Prover-private witness, advice, randomness, and mutable state
belong to an external strategy or a dependent Interface/Plan. They never occur
as concrete values in `CoreId`.

A general interactive Core may declare Verifier-private invocation values.
Their existence is identity-bearing and their visibility is exactly Verifier.
Section 11 rejects any such value or its dependency closure from an FS-eligible
Core.

### 4.2 Inputs and value references

```text
PublicInputDecl = { value_type: ValueType }

VerifierPrivateInputDecl = { value_type: ValueType }

TypedConstantDecl = {
  value_type: ValueType,
  value: CanonicalValue<value_type>
}

ValueRef =
    PublicInput(PublicInputRef)
  | VerifierPrivateInput(VerifierPrivateInputRef)
  | Constant(ConstantRef)
  | Derived(DerivedValueRef)
  | OccurrenceOutput(OccurrenceRef, output_ordinal)

TypedValueRef = { ref: ValueRef, value_type: ValueType }
```

The repeated `value_type` is checked metadata: admission derives the referenced
type and requires exact equality. It is included in canonical bodies only where
Appendix A says so; a cache may not override derivation.

```text
DerivedValueDecl = {
  algorithm: PortableAlgorithmRef,
  evaluation_contract: EvaluationContractId,
  inputs: CanonicalSeq<ValueRef>,
  result_type: ValueType
}
```

The algorithm's admitted derived ABI must have the exact ordered input types,
the exact `result_type`, and an empty semantic-failure row. A value whose
mathematical operation is partial must use a total tagged result value and make
the branch explicit; an unhandled algorithm failure cannot be hidden as value
absence.

`ValueRef` availability to the execution engine is derived from initial
inputs/constants, earlier occurrence outputs, and the topological
`derived_values` order. A derived value may read only available operands. This
engine availability does not grant a strategy access to an invocation input;
Section 9.2 separately derives the scope-gated `ProverView`, and a
Verifier-private input never enters it. There is no generic ambient value, host
object, callback, or late registry lookup.

### 4.3 Public binding classes

```text
PublicBindingClass = Statement | SessionContext | PublicParameter

PublicBindingDecl = {
  scope: ScopeRef,
  class: PublicBindingClass,
  value: ValueRef
}
```

- `Statement` fixes the exact public claim or instance for that scope.
- `SessionContext` distinguishes application/session use without asserting
  proof freshness or replay prevention by itself.
- `PublicParameter` is a runtime public value affecting verifier behavior;
  a static parameter belongs directly in the Core or construction body.

Every public input is named directly by at least one binding. No
Verifier-private value may be a public binding. The same value may have
distinct binding occurrences in different scopes; each occurrence has its own
`BindingRef` and transcript coordinate. Duplicate `(scope, class, value)`
triples refuse because they add no distinguishable meaning.

### 4.4 Explicit scopes

```text
ScopeOpening = Initially | BeforeOccurrence(OccurrenceRef)

ScopeDecl = {
  parent: None | Some(ScopeRef),
  opening: ScopeOpening
}
```

Scope 0 is the unique root, has no parent, and opens `Initially`. Every other
scope names an earlier scope as parent and opens before one occurrence. Scope
depth is bounded. A scope's binding sequence is derived by scanning
`PublicBindingDecl` in ascending `BindingRef` order; there is no second authored
backlink list.

A child opens after its parent and after every value in its bindings is
available. It opens at most once. At least one occurrence belongs to it. A
scope cannot open after its first occurrence or after any challenge assigned
to that scope. An occurrence's active scope is explicit; its ancestors must
already be open.

Scope opening is not a caller event or strategy move. It is a deterministic
semantic boundary used by visible-history and transcript derivation. The
transcript remains continuous across openings. At each boundary, let `Due(b)`
be every unopened scope whose `opening` is `Initially` at the initial boundary
or `BeforeOccurrence(b)` at the named occurrence boundary. Admission requires
that the root is the only initially due scope. Before occurrence `b`, execution
opens all members of `Due(b)` in ascending `(scope_depth, ScopeRef)` order;
therefore a simultaneously due parent always opens before its child, and
siblings open by ascending ordinal. Each opening emits its bindings in
ascending `BindingRef` order before the next scope opens. A due scope whose
parent is neither already open nor earlier in that exact order refuses
admission. No implementation traversal order may replace this order.

## 5. Guards, challenges, and occurrence order

### 5.1 Guards

```text
Guard =
    Always
  | EvaluateBoolean {
      algorithm: PortableAlgorithmRef,
      evaluation_contract: EvaluationContractId,
      inputs: CanonicalSeq<ValueRef>
    }
```

The algorithm must be admitted, total on the exact input domains, return the
K1 Boolean value type, and have an empty failure row. Inputs are available
before the guarded occurrence. A guard is evaluated exactly once. The result
is public only if all input dependency leaves are public; Prover visibility is
computed, not asserted.

There is no canonical decision diagram or extensional equivalence claim.
Changing the algorithm reference or operands changes the Core body even when
an Analysis relation could later prove equivalent behavior.

### 5.2 Challenge declarations

```text
CoinCorrelation =
    Independent
  | JointMember {
      group: ProtocolDeclarationRef<"pir.coin-correlation-group">,
      index: ordinal,
      prior_members: CanonicalSeq<ChallengeRef>
    }

ReductionUsePolicy =
    Exclusive
  | Shared(
      ProtocolDeclarationRef<"pir.challenge-sharing-contract">)

ChallengeDecl = {
  scope: ScopeRef,
  value_type: ValueType,
  domain: ProtocolDeclarationRef<"pir.challenge-domain">,
  fresh_law: ProtocolDeclarationRef<"pir.public-coin-law">,
  correlation: CoinCorrelation,
  reduction_use: ReductionUsePolicy,
  public_conditions: CanonicalSeq<ValueRef>
}
```

Each Challenge has exactly one occurrence and one output. Its public
conditions are available and public before that occurrence. Independent draws
have no prior member. Joint members use dense indices from zero, one exact
group, compatible laws and types, and list every earlier member required by
the conditional law in group order. A group may not mix scopes unless its
declaration explicitly uses their least common active ancestor.

Challenge domains are semantic-purpose coordinates and may repeat. Distinct
draws remain distinct because the Fiat--Shamir namespace contains the exact
scope path and `ChallengeRef`. A shared value is represented by one Challenge
occurrence referenced at multiple legal consumers, not by two declarations
with the same domain. Joint members represent correlated but distinct draws.

Section 6.3 derives the sorted-unique `ReductionConsumers(c)` from exact
reduction declarations; a value dependency or equal challenge value does not
create such a consumer. `Exclusive` requires
`|ReductionConsumers(c)| <= 1`. `Shared(contract)` requires
`|ReductionConsumers(c)| >= 2`, binds that complete derived consumer sequence
to the exact sharing-contract coordinate, and permits no consumer outside the
sequence. Every consumer uses this one Challenge occurrence and its one output,
not a copied or equal-valued draw. The sharing declaration is a coordinate for
the K3 property/pricing obligation; its nominal body does not itself prove that
reuse is sound. Ordinary value uses by checks and deterministic computations
are not reduction-role uses.

The Fresh law denotes a distribution independent of prover-controlled history,
conditioned only on its named earlier public-coin members and public static
conditions. Distribution truth is an Analysis/evidence obligation. PIR checks
the exact structural dependency surface.

### 5.3 Occurrence envelope

```text
OccurrenceDecl = {
  scope: ScopeRef,
  guard: Guard,
  effect: CoreEffect
}

CoreEffect =
    ProverMessage(ProverMessageDecl)
  | DeterministicVerifierMessage(VerifierMessageDecl)
  | Challenge(ChallengeRef)
  | InvokeCheck(CheckRef)
  | ApplyReduction(ReductionRef)
  | ReachTerminal(TerminalRef)
  | StandardOracle(OracleEffect)
  | ModuleEffect(ModuleEffectRef)
```

The sequence ordinal is the `OccurrenceRef`; no second schedule field exists.
It is the exact semantic order. Every `ValueRef`, guard input, scope opening,
claim use, query, and reduction reference obeys the earlier-boundary laws on
this page.

An occurrence is attempted iff execution is live, its scope is open, and its
guard evaluates true. An inactive occurrence emits no Core output. The
Fiat--Shamir page separately decides when an exact inactive marker is required
to distinguish transcript histories.

### 5.4 Messages

```text
MessageChannelRef = ProtocolDeclarationRef<"pir.message-channel">

ProverMessageDecl = {
  channel: MessageChannelRef,
  payload_type: ValueType
}

VerifierMessageDecl = {
  channel: MessageChannelRef,
  algorithm: PortableAlgorithmRef,
  evaluation_contract: EvaluationContractId,
  inputs: CanonicalSeq<ValueRef>,
  payload_type: ValueType
}
```

An active `ProverMessage` is a strategy decision expecting one canonical value
of `payload_type`; output 0 is that value and becomes visible to both parties.
An active deterministic Verifier message evaluates its exact total, failure-
free algorithm; output 0 becomes visible to both parties. A verifier message
whose value is selected by hidden state or a supplier is not this constructor.

Messages have no authored Wire/Transcript switch. Wire exposure belongs to
Interface/OIR; transcript influence is derived by the companion page.

## 6. Checks, claims, reductions, and terminals

### 6.1 Checks

```text
CheckDecl = {
  algorithm: PortableAlgorithmRef,
  evaluation_contract: EvaluationContractId,
  inputs: CanonicalSeq<ValueRef>
}
```

The admitted algorithm has the exact input ABI, Boolean success type, and
empty failure row. Cryptographic or backend-specific operations enter through
exact K1 semantic primitives used by that portable algorithm; there is no
second opaque check callback. Missing primitive/evaluator support is
operational `Unsupported`, not false. A successful active check creates
Boolean output 0, visible to Verifier and to Prover only if a later public
message or terminal exposes it.

Checks are predicates over already available values. Their existence proves no
relation satisfaction or cryptographic property.

### 6.2 Claims

```text
ClaimUsage = Linear | Reusable

ClaimSource =
    InitialClaim(BindingRef)
  | ReductionOutput(ReductionRef, output_ordinal)

ClaimDecl = {
  contract: ProtocolDeclarationRef<"pir.claim-contract">,
  scope: ScopeRef,
  usage: ClaimUsage,
  source: ClaimSource
}
```

An initial claim cites a Statement binding in the same scope or an ancestor.
A reduction output has the exact contract declared for that output. A claim is
live only after its source exists. A linear claim can be consumed or discharged
once. A reusable claim can be cited repeatedly but remains subject to terminal
disposition.

### 6.3 Reductions

```text
ReductionPublicationRequirement = {
  publication: OccurrenceRef,
  next_challenge: None | Some(ChallengeRef)
}

ReductionDecl = {
  contract: ProtocolDeclarationRef<"pir.reduction-contract">,
  scope: ScopeRef,
  input_claims: NonEmptyCanonicalSeq<ClaimRef>,
  side_inputs: CanonicalSeq<ValueRef>,
  required_challenges: CanonicalSeq<ChallengeRef>,
  required_publications: CanonicalSeq<ReductionPublicationRequirement>,
  output_contracts:
    CanonicalSeq<ProtocolDeclarationRef<"pir.claim-contract">>
}
```

An active `ApplyReduction` requires every input claim live, every side input
available, and every required challenge and publication already occurred. The
exact reduction contract fixes the structural role and output-claim ABI. The
occurrence consumes each linear input and creates its declared outputs in
ordinal order. It does not execute a proof theorem; K3 assigns property meaning
to the admitted structural transition.

`ReductionPublicationOccurrence(o)` is derived, never asserted. It is true
exactly when `o` carries a `ProverMessage`, a `PublishOracle`, or a supported
`ModuleEffect` whose admitted effect declaration gives it the exact
`ProverPublication` decision class and a public module observation. A
deterministic Verifier message, Challenge, Oracle Query/Answer, Check,
Reduction, or Terminal cannot inhabit this slot.

For one reduction, `required_challenges` has no duplicate and is ordered by the
occurrence positions of its one-to-one Challenge occurrences.
`required_publications` has no duplicate `publication` and is ordered by those
publication occurrence positions. The one `ApplyReduction` occurrence has
exactly the reduction's declared scope. Every named Challenge and publication
has that scope or an ancestor on its active scope path, is guard-available
under `GuardImplies`, and precedes `ApplyReduction`. A future,
inactive-on-the-use-path, wrong-kind, or wrongly scoped entry refuses admission.

For a publication requirement `p`:

- `Some(c)` requires `c` in this reduction's `required_challenges`, requires
  `p.publication` to precede the occurrence of `c`, and requires `c` to be the
  **least** required challenge occurring after that publication; and
- `None` is legal exactly when no required challenge follows the publication.
  If the reduction has a required challenge, such a publication therefore
  follows its last required challenge.

Consequently, every reduction-owned publication before a later round challenge
has one mechanically determined `next_challenge`; the Fiat--Shamir construction
adds that publication occurrence to `RequiredInfluence(c)`. Cumulative
transcript state carries it to still later challenges. A Schnorr response may
legally use `None` after its last challenge, whereas material placed before a
later batching challenge cannot be mislabeled as a post-challenge response.
This is the K2 Last-Challenge law.

Every `ReductionPublicationOccurrence` in the transitive value-dependency
closure of `side_inputs` must occur exactly once in `required_publications`.
The declaration may name an additional publication when the selected reduction
contract assigns it a semantic round role not visible in value dataflow; naming
it makes that occurrence reduction-owned for all K2 ordering and influence
checks. K3 must check that this exact structural role set is adequate for the
reduction contract's property rule; PIR does not infer theorem roles from a
label.

Define one reduction-role consumer as the pair `(ReductionRef, ChallengeRef)`
for each unique membership of `ChallengeRef` in that reduction's
`required_challenges`, and define:

```text
ReductionConsumers(c) =
  sort_unique_by(
    (position(ApplyReduction(reduction)), ReductionRef),
    every (reduction, c))
```

Each consumer's Challenge occurrence precedes its `ApplyReduction`, and every
publication linked to that challenge satisfies the law above. The complete
derived sequence is checked against the Challenge's `ReductionUsePolicy` in
Section 5.2. Equal values, equal domains, ordinary dataflow uses, and repeated
references inside one reduction create no additional consumer.

### 6.4 Terminals

```text
TerminalVerdict = Accept | Reject | Abort

ClaimDisposition = Consume | Discharge

TerminalDecl = {
  verdict: TerminalVerdict,
  public_outputs: CanonicalSeq<ValueRef>,
  required_true_checks: CanonicalSeq<CheckRef>,
  claim_dispositions:
    CanonicalSeq<(ClaimRef, ClaimDisposition)>
}
```

At an active terminal, every public output is available to Verifier, every
required check has occurred and is true, and every named claim is live. Its
dispositions apply in sequence, then every live linear claim must be consumed
or discharged and every accepting-path required reduction must be saturated.
An `Accept` terminal additionally rejects an unresolved initial claim or
unapplied required reduction. `Reject` and `Abort` may discharge remaining
claims only through explicit dispositions.

Each Terminal has exactly one occurrence. The final Core occurrence is an
unconditional `ReachTerminal` in the root or an open descendant scope, ensuring
a finite fallback. Execution stops at the first active terminal. Earlier
guarded terminals are allowed.

## 7. Standard immutable-oracle extension

### 7.1 Oracle declarations

```text
OraclePublicationMode =
    FullCanonicalOracle
  | PublicBinding {
      binding_type: ValueType,
      binding_contract:
        ProtocolDeclarationRef<"pir.oracle-binding-contract">,
      binding_algorithm: PortableAlgorithmRef,
      evaluation_contract: EvaluationContractId
    }

OracleDecl = {
  scope: ScopeRef,
  index_type: ValueType,
  element_type: ValueType,
  maximum_entries: Natural, // 0 .. 2^14
  publication_mode: OraclePublicationMode
}

OracleEntryType(o) =
  RootRecord<[(0, o.index_type), (1, o.element_type)]>

OracleCarrierType(o) =
  RootSeq<OracleEntryType(o), o.maximum_entries>

OracleLookupResultType(o) =
  RootVariant<[(0, RootUnit), (1, o.element_type)]>

CanonicalFiniteOracle<o> = CanonicalValue<OracleCarrierType(o)>

OraclePublicationOutputType(o) =
  if o.publication_mode = FullCanonicalOracle
  then OracleCarrierType(o)
  else o.publication_mode.binding_type

OracleAnswerOutputType(o) = OracleLookupResultType(o)
```

The three root-type constructors above are the exact K1 aliases in the Core's
semantic regime; `0` and `1` are exact record/case ordinals. A finite Oracle's
admitted datum is exactly:

```text
S[ R{0:index_0.datum,1:element_0.datum}, ... ]
```

Formation requires `0 <= maximum_entries <= 2^14` and requires the complete
`OracleCarrierType(o)` to pass K1's `Worst` byte, node, edge, and depth bounds.
The local `2^14` ceiling is therefore not a promise that every entry type can
inhabit that capacity; larger index or element types may force a smaller
formable maximum. The sequence length is at most `maximum_entries`; every index
and element is owner-admitted at its declared type; entries are strictly
ascending by `index.canonical_bytes`; and indices are unique under the
Foundation domain-owned equality for the exact `index_type`. Unique canonical
representatives make an equal index have equal canonical bytes, but lookup
uses the domain-owned equality, not host byte equality or a language map.

`Lookup(o, index)` scans that bounded sequence in order and returns the exact
`OracleLookupResultType(o)` value `V(0,Unit)` when absent or
`V(1,element.datum)` for the unique equal index. This total definition removes
an ambient missing-index exception. Publication output and Answer output have
the exact derived types above; neither output type is inferred from a receipt.

The Oracle carrier is strategy-supplied once at publication, strictly admitted
as `CanonicalFiniteOracle<o>`, and snapshotted immutably by the execution
engine. `FullCanonicalOracle` publishes that exact carrier. `PublicBinding`
keeps the carrier confidential and publishes the result of the named admitted,
total, failure-free algorithm whose exact ABI is
`[OracleCarrierType(o)] -> binding_type`. Its evaluation contract is checked by
K1. The nominal binding contract records the intended cryptographic relation
for K3; it does not replace executable binding computation or prove the
relation secure.

### 7.2 Oracle effects

```text
OracleEffect =
    PublishOracle(OracleRef)
  | QueryOracle {
      oracle: OracleRef,
      index: ValueRef,
      visibility: Public | VerifierOnly
    }
  | AnswerOracle {
      query: OccurrenceRef
    }
```

Each Oracle has exactly one `PublishOracle`, and that occurrence's scope equals
`OracleDecl.scope`. Publication is a prover decision, output 0 has
`OraclePublicationOutputType(o)`, and both parties observe that exact public
value. There is no second strategy-supplied `public_material` that could
disagree with it.

A Query occurs strictly after publication, uses one available value of exact
`index_type`, and lies in the Oracle scope or a descendant whose scope path
contains it. Its guard must imply the publication guard. `VerifierOnly` means
the index and answer remain verifier-visible and makes every dependent sink
fail Section 11; a Public query coordinate is visible to both parties. Query
has no Core output.

`AnswerOracle` names one earlier unmatched Query, has exactly the Query's scope
and visibility, and its guard must imply the Query guard. It performs
`Lookup(o,index)` and creates output 0 of exact
`OracleLookupResultType(o)`. Every active Query has exactly one active Answer
before any dependent use or terminal; an inactive Query has no Answer on that
path. Wrong Oracle, wrong index type, answer before query, duplicate answer,
scope/guard mismatch, mutation after publication, or a recorded answer unequal
under Foundation equality at that exact result type refuses generation/replay
at the first affected boundary.

Replay reconstructs a `FullCanonicalOracle` by strict decoding of its
publication output. For `PublicBinding`, the replay capability supplies one
exact `CanonicalFiniteOracle<o>`; replay reruns the binding algorithm and
requires Foundation equality with the recorded publication output. It then
recomputes every Query index from the Core state and every Answer with
`Lookup`, comparing the receipt and occurrence output at their exact types.
Missing/extra Oracle witnesses or receipts refuse; unsupported domain equality
or binding evaluation is qualified noncompletion, never a successful match.

A commitment root, authentication path, and opening check are ordinary public
values/messages/checks around this lifecycle. They do not replace the logical
Oracle or allow an answer to define it retroactively.

## 8. Exact-used semantic extensions

A Core constructor outside Sections 5--7 is a `ModuleEffectRef`:

```text
ModuleEffectRef = {
  module: SemanticModuleId,
  declaration: ModuleDeclarationRef<"pir.core-effect">,
  payload: MetaValueV0
}
```

The declaration module must be in `used_modules`. Its authenticated local body
fixes the effect's exact payload schema, inputs and outputs, actor-visible
history, transition, guard behavior, required-influence rule, replay rule,
terminal interaction, and deterministic work bounds. It also fixes exactly one
decision class (`NoProverDecision`, `ProverDecision`, or
`ProverPublication`), a finite ordered dependency edge list for every output
and control result, and, for each deterministic public output, an exact admitted
portable reconstruction algorithm plus evaluation contract over those ordered
dependencies. `ProverPublication` additionally requires one public
`ModuleObservation`. Every outward `ValueType` is lifted under K1. The evaluator
must advertise support for that exact module and effect declaration before
owner admission. A declaration cannot supply a `publicly_recomputable` Boolean
or other asserted classification in place of these executable facts.

Unknown same-kind semantics are `Unsupported`; wrong kind/regime is
`KindMismatch`; malformed payload is `Malformed`; a supported well-formed
payload failing its owner law is `Refused`. No opaque effect, callback, or
authored observation set is accepted. Adding a supported module does not rotate
unrelated Core IDs; only Cores importing it cite its ID.

The Core's direct module set is a derived function:

```text
DirectOwnerModules(C) = sort_unique_by(ContentRefV0, modules from)
  1. ModuleOwner(x) for every ProtocolDeclarationRef x in C;
  2. the owner of every module-owned ValueDomainRef recursively present in
     any ValueType or typed constant in C;
  3. ModuleEffectRef.module and ModuleOwner(ModuleEffectRef.declaration),
     which admission requires to be equal; and
  4. every module owner in a declaration-reference or value-type slot obtained
     by strict decoding of a ModuleEffect payload under its exact owner schema.

ExactUsedModules(C) := C.used_modules = DirectOwnerModules(C)
```

Equality is equality of the complete sorted `SemanticModuleId` sequence. An
omitted direct owner and an unreferenced extra owner both refuse admission.
Imports of these direct owners are authenticated through K1's derived
`RequiredModuleClosure_B(DirectOwnerModules(C))`; transitive imports are not
silently copied into `used_modules` unless a Core field directly cites them.
Portable algorithms and evaluation contracts authenticate their own exact
closures and do not donate hidden modules to the Core's direct list.

## 9. Visible history and legal prover decisions

### 9.1 Observations

```text
Observation =
    PublicBindingOpened(BindingRef, CanonicalValue)
  | MessageObserved(OccurrenceRef, Party, CanonicalValue)
  | ChallengeObserved(OccurrenceRef, CanonicalValue)
  | OraclePublished(OccurrenceRef, OracleRef, public_material)
  | OracleQueryObserved(OccurrenceRef, OracleRef, CanonicalValue)
  | OracleAnswerObserved(OccurrenceRef, CanonicalValue)
  | PublicTerminalObserved(OccurrenceRef, TerminalRef,
                           TerminalVerdict, public_outputs)
  | ModuleObservation(OccurrenceRef, ModuleEffectRef,
                      module_defined_payload)
```

`VisibleHistory(party, boundary)` is the exact subsequence of occurred
observations visible to that party before the boundary, preserving Core order
and scope-opening positions. Prover additionally knows every move it supplied
and its strategy-private state; those are not public observations. Verifier
additionally knows its declared private inputs, Verifier-only oracle queries
and answers, and internal check results.

An object being used by transcript, a check, or a claim is not an implicit
knowledge transfer. Visibility follows only the constructors above and an
exact supported module rule.

### 9.2 Decision points and views

```text
ProverDecisionKind =
    SupplyMessage(payload_type)
  | SupplyOracle(oracle_schema, publication_mode)
  | ModuleDecision(module_defined_type)

ProverDecisionPoint = {
  occurrence: OccurrenceRef,
  scope_path: NonEmptyCanonicalSeq<ScopeRef>,
  kind: ProverDecisionKind
}

ProverDecisionPointRef =
  OccurrenceRef restricted to an occurrence whose effect is
    ProverMessage
  | PublishOracle
  | supported ModuleEffect with decision class
      ProverDecision or ProverPublication

ProverMove =
    MessageValue(CanonicalValue<declared payload type>)
  | OracleValue {
      immutable_oracle: CanonicalFiniteOracle<declared Oracle>
    }
  | ModuleMove {
      declaration: exact ModuleEffectRef,
      payload: exact module-defined canonical value
    }

ProverView = {
  protocol_id: ProtocolId,
  static_protocol_view: PublicProtocolDescriptionView,
  public_invocation: CanonicalSeq<(PublicInputRef, CanonicalValue)>,
  visible_history: CanonicalSeq<Observation>,
  current_decision: ProverDecisionPoint
}
```

`ProverDecisionPointRef` is therefore a Core-local dense occurrence ordinal,
not a second authored sequence or an ordinal into a derived host table. The
`occurrence` field of the point denoted by `d` is exactly `d`. Its `scope_path`
and `kind` are owner-derived from that occurrence and, for a module effect, its
exact admitted declaration.

`PublicProtocolDescriptionView` is the immutable tuple of exact `ProtocolId`,
admitted Core declaration/view, and, for an FS Protocol, the exact admitted
transcript-construction declaration. It exposes static public declarations and
schedule shape, never invocation values or mutable execution state. Knowing
the protocol is not anticipation. Define `ProverInputOpening(i)` as the least
scope-opening boundary, in Section 4.4's exact deterministic boundary order,
among the direct public bindings whose value is `PublicInput(i)`.
`public_invocation` contains every and only declared public input whose
`ProverInputOpening` has occurred, in `PublicInputRef` order. A root-bound input
is therefore present from initialization; an input bound only in a child scope
first appears when that scope opens and remains visible thereafter. The binding
occurrence is still distinct: its own scope determines when it becomes an
observation and influences a transcript. The view contains only observations
that have occurred. It contains no future runtime value or receipt, future
coin, verifier-private value, unqueried oracle answer, mutable transcript state,
ambient registry, clock, file, or process object.

For dependent Plans, K2 exports one structural read predicate rather than a
caller-asserted snapshot predicate:

```text
K2ProverReadCoordinate =
    StaticConstant(ConstantRef)
  | PublicInvocationInput(PublicInputRef)
  | OpenedBinding(BindingRef)
  | ObservedMessage(OccurrenceRef)
  | ObservedChallenge(OccurrenceRef)
  | ObservedOraclePublication(OccurrenceRef)
  | ObservedOracleQuery(OccurrenceRef)
  | ObservedOracleAnswer(OccurrenceRef)
  | ObservedModuleValue(OccurrenceRef, observation_ordinal)
  | PriorOwnMove(ProverDecisionPointRef)

GuaranteedProverRead(d: ProverDecisionPointRef,
                     r: K2ProverReadCoordinate) = true
  exactly under the owner rules below
```

Constants are guaranteed at every decision. `PublicInvocationInput(i)` is
guaranteed exactly when `ProverInputOpening(i)` is no later than
`BeforeOccurrence(d)`; a child-only input cannot be read by an earlier parent
decision. `OpenedBinding(b)` is guaranteed exactly when the deterministic
opening boundary of `b` is no later than `BeforeOccurrence(d)`. An observation
or prior move is guaranteed exactly when its exact source occurrence precedes
`d`, its source kind and output coordinate match the requested constructor,
its K2 visibility includes Prover, the source scope and every ancestor on its
declared scope path deterministically open before `d`, and
`GuardImplies(guard(d), guard(source))`. For a module observation, the supported
declaration must export that exact ordinal as Prover-visible. For a Public
Oracle query or answer visibility includes Prover; a Verifier-only coordinate
never passes. `PriorOwnMove` additionally requires the named source to be an
exact earlier prover decision.

These checks use Core order, deterministic scope ancestry/opening, owner-derived
visibility, and the closed Section 10 `GuardImplies` rule only. Since a run that
reaches `d` has not taken an earlier terminal, they establish that `r` is in
every legal `ProverView` in which `d` is active. A mathematically stronger guard
implication, one sample run, or a caller-provided history cannot widen this
predicate. A dependent `PlanRealizes` judgment must use
`GuaranteedProverRead`; membership in one supplied runtime view is
insufficient.

```text
StrategyStep(private_state, ProverView, private_randomness)
  -> Produce(ProverMove, next_private_state)
   | Stop
```

PIR defines this relation and the legal move grammar, not a strategy language
or identity. The capability is bound to the exact `ProtocolId`; a realization
invokes it through an interface that can read only `ProverView` plus its
supplied private state/randomness. A dependent Plan may identify a particular
strategy implementation without changing the Core.

`Stop`, unavailable capability, private search exhaustion, or failure to
produce a legal move yields operational noncompletion and no Core terminal.
An explicit protocol abort is a public move followed by ordinary terminal
logic.

## 10. Core admission

`AdmitCore` evaluates these boundaries in order:

1. authenticate the prior-meta basis, Core ID/body, every asserted direct
   module ID/body pair, all ordinary references, algorithms, contracts, and the
   K1-derived transitive module closures inside one hash-binding ledger;
2. validate Appendix A carrier shape, all bounds, dense ordinals, sorted-unique
   sets, exact reference kinds/regimes, and absence of trailing or unknown
   fields;
3. derive `DirectOwnerModules(core)`, require `ExactUsedModules(core)`, reject
   omitted and extra module IDs, resolve and support every exact-used PIR
   declaration and extension, derive every algorithm ABI, and refuse an unknown
   constructor;
4. type constants, inputs, derived values, guards, messages, checks,
   challenges, oracles, claims, reductions, terminals, and occurrence outputs;
5. validate the rooted scope tree, the exact simultaneous-opening order,
   binding completeness and uniqueness, value availability, and occurrence
   scope membership;
6. validate the total occurrence order, guard availability, one-to-one
   Challenge/Check/Reduction/Terminal/Oracle occurrence backlinks, the exact
   finite-Oracle carrier/lookup/output laws, and standard effect lifetime and
   scope rules;
7. derive party visibility and reject a use that is unavailable to its actor;
8. validate challenge laws, joint-group closure, derived namespace
   distinguishability, the exact `ReductionConsumers` sequence, and its
   `Exclusive`/`Shared` law;
9. simulate structural claim liveness on every schedule path induced by the
   finite guards, using the Core's bounded explicit state, and check linearity,
   required-publication kind/uniqueness/least-next-challenge order,
   Last-Challenge closure, reduction saturation, and terminal closure; and
10. require the unconditional final fallback terminal and mint one immutable
    `AdmittedCore` only if every boundary succeeds.

Step 9 does not enumerate Boolean assignments or build an ROBDD. K2 uses a
finite forward abstract state and one closed syntactic implication law:

```text
GuardImplies(use_guard, source_guard) :=
  source_guard = Always or use_guard = source_guard
```

A guarded use of a conditionally produced value, claim, query, or other state
must pass this law. A mathematically valid but syntactically different
implication is not guessed, delegated to a host solver, or accepted by an
unidentified certificate; it is outside this K2 regime. A future checked
implication satellite would require its own exact proposition, validator,
bounds, and admission integration.

Admission is deterministic and bounded by the K1 body limits plus linear scans,
sorted-set operations, algorithm checks, and the finite abstract-state
transfer. It constructs no exponential decision diagram.

## 11. Structural public-coin eligibility

`PublicCoinEligible(AdmittedCore)` is computed by one finite dependency
analysis, not read from an authored flag. Its closed coordinate algebra is:

```text
PCNode =
    PublicInputNode(PublicInputRef)
  | VerifierPrivateInputNode(VerifierPrivateInputRef)
  | ConstantNode(ConstantRef)
  | DerivedValueNode(DerivedValueRef)
  | ScopeOpeningNode(ScopeRef)
  | BindingObservationNode(BindingRef)
  | OccurrenceActivityNode(OccurrenceRef)
  | OccurrenceEffectNode(OccurrenceRef)
  | OccurrenceOutputNode(OccurrenceRef, output_ordinal)
  | ClaimStateNode(ClaimRef)
  | ReductionStateNode(ReductionRef)
  | TerminalDecisionNode(TerminalRef)
  | ModuleControlNode(OccurrenceRef, control_ordinal)
  | ModuleOutputNode(OccurrenceRef, output_ordinal)
```

`PCNodeBody` in Appendix A fixes these tags and fields. `ValueProducerNode`
maps every `ValueRef` to its unique input, constant, derived-value, or
occurrence-output node. Construct `PCGraph(core)` with exactly the applicable
nodes above and the following edges:

1. a derived-value node receives its declared input producer nodes;
2. a scope-opening node receives its parent opening, and a binding-observation
   node receives its scope opening and bound value producer;
3. occurrence activity receives its scope opening and exact guard producers;
4. occurrence effect receives activity plus all constructor operands:
   message/check inputs, challenge conditions and prior joint members, Oracle
   publication/query dependencies, reduction claims/side inputs/challenges/
   publications, terminal checks/claims/public outputs, or the exact supported
   module dependency list;
5. every occurrence output receives its effect node; claim, reduction, and
   terminal nodes receive their exact source/effect nodes; and
6. module control/output nodes receive precisely the declaration-owned ordered
   edges, with every outward module output connected to its occurrence output.

No implicit schedule-prefix edge is added: order alone is not data or control
dependence. Admission has already made the resulting graph acyclic and forward;
the graph is bounded by Section 2. Its deterministic topological order is
Kahn's algorithm, selecting at each step the available node with the least
`M(PCNodeBody(node))`; failure to exhaust every node refuses admission.

Evaluate its unique topological order in the lattice:

```text
PCClass = StaticPublic | PublicHistory | VerifierPrivate | Invalid

Join(xs) = Invalid          if Invalid in xs
         | VerifierPrivate  else if VerifierPrivate in xs
         | PublicHistory    else if PublicHistory in xs
         | StaticPublic     otherwise

Publish(x) = PublicHistory  if x in {StaticPublic, PublicHistory}
           | x              otherwise
```

Public inputs and constants are `StaticPublic`; Verifier-private inputs are
`VerifierPrivate`. Total failure-free derived algorithms, guards, scope
openings, checks, reductions, and terminals use `Join` of their exact incoming
edges. A Prover message, Oracle publication output, or Public Oracle answer uses
`Publish(activity)`; a Public Query uses `Join(activity,index)`, while a
Verifier-only Query/Answer is `VerifierPrivate`. A deterministic Verifier
message uses `Join(activity,inputs)` only after its exact K1 ABI check. A
Challenge is `PublicHistory` only when its activity is public, every
`public_condition` is `StaticPublic`, and every named joint member is an earlier
valid Challenge; otherwise it is `Invalid` or `VerifierPrivate` by the first
failed dependency. Any other nondeterministic Verifier-to-Prover output is
`Invalid`.

A module effect applies these same transfers to its exact dependency edges:
Prover publications use `Publish`, and deterministic public outputs use the
declared reconstruction algorithm after ABI checking. A missing edge,
unsupported reconstruction algorithm, asserted Boolean classification, or
Verifier nondeterminism yields `Invalid`.

For a supported module, the authenticated edge and sink declarations are the
effect's semantic dependency law rather than evidence about a host
implementation. Admission validates and applies that law. Realization and
Evidence must show that an implementation has no undeclared dependency; a host
that reads one is nonconforming and does not change `PublicCoinView`.

`PCSinks(core)` is the derived set of every guard/activity controlling a public
observation, deterministic Verifier output, public Query index, Challenge
condition, invoked Check, Reduction transition, Terminal decision, terminal
public output, and module control/output declared acceptance-relevant.
`PublicCoinEligible(core)` is true exactly when every sink is
`StaticPublic` or `PublicHistory`, every Challenge passed its special transfer,
and every challenge is observed before a later Prover-decision dependency may
consume it. Unused Verifier-private inputs are therefore harmless; any path
from one to a sink is mechanically rejecting. The finite node/edge tables and
final classes are retained in `PublicCoinView`.

This predicate proves no distribution, independence, soundness, or random-
oracle property. It identifies the exact Core structure for which a
Fiat--Shamir interpretation can be formed. A false result refuses FS admission
but does not invalidate the Fresh Core.

## 12. Challenge-parameterized execution

### 12.1 Resolver interface

Core execution is parameterized only by an admitted challenge resolver:

```text
ResolveChallenge(
  admitted_core,
  challenge_ref,
  public_history,
  exact public conditions,
  prior joint members)
  -> Success(CanonicalValue<challenge.value_type>)
   | typed interpretation DomainFailure
   | qualified operational noncompletion
```

`FreshResolver` obtains one exact value from a scoped public-coin capability
and records the Challenge's declared-law coordinate. The value must be in the
exact domain. A concrete source, supplier, device, or observation coordinate
is not part of the K2 semantic receipt; Analysis or Evidence may bind such
provenance separately without changing the Protocol or pretending that source
identity proves a distribution. One sample cannot establish that the
capability followed the distribution. `FiatShamirResolver` is defined by the
companion page. No other resolver may inhabit an admitted Protocol.

### 12.2 Invocation and state

```text
CoreInvocation = {
  public_inputs:
    TotalMap<PublicInputRef, CanonicalValue<declared type>>,
  verifier_private_inputs:
    TotalMap<VerifierPrivateInputRef, CanonicalValue<declared type>>
}

CoreState = {
  next_occurrence,
  open_scopes,
  canonical_values,
  party_visible_histories,
  immutable_oracles,
  pending_queries,
  check_results,
  live_claims,
  applied_reductions,
  optional_terminal
}

CoreInvocationId = ProfiledSemanticId<"pir.invocation">(
  B, PIRInteractionProfileId,
  CoreInvocationBody(admitted_core.id, invocation))
```

Input maps cover every and only declared occurrence. Strict canonical decode
and domain admission precede execution. State collections use declaration
ordinals and are bounded by the Core. `CoreInvocationBody` is fixed in
Appendix A. The invocation handle and ID may be confidential when the Fresh
Core has Verifier-private inputs; content addressing never authorizes
disclosure.

The capability arguments and evaluation control are exact runtime bindings,
not semantic shortcuts:

```text
ChallengeResolverCapability = one resolver admitted by Protocol interpretation
ExecutionEvaluationControl = {
  evaluator: exact K1 evaluator,
  per_request_limits: PortableEvaluationLimitsV0
}
ExactCheckAndExtensionCapabilities =
  total bindings for every used primitive/module effect
ExactOracleReplayCapabilities =
  TotalMap<PublicBinding OracleRef, CanonicalFiniteOracle<declared Oracle>>
```

Each binding is checked against the ID or declaration already committed by the
admitted subjects. Missing support is qualified noncompletion; a disagreeing
provider is `CheckerFailure`. `ExecutionEvaluationControl` is an immutable
snapshot for one generated or replayed run. Every K1 algorithm request starts
fresh counters under its exact finite `per_request_limits`; the limits and
charges are ephemeral evaluator control and enter no Core, Protocol,
construction, invocation, or record identity.
Its `evaluator` must be the identical evaluator retained by the admitted
Protocol handle. Only the finite limits may vary between calls. Portable use by
another evaluator requires cold reauthentication and readmission of the Core,
construction when present, and Protocol before execution.

### 12.3 Generated run

```text
GenerateRun(
  AdmittedProtocol,
  CoreInvocation,
  ProverStrategyCapability,
  ChallengeResolverCapability,
  ExactCheckAndExtensionCapabilities,
  ExecutionEvaluationControl)
  -> CompletedRun(RunRecord, CausalGenerationCapability)
   | InterpretationFailed(ProtocolFailureRecord)
   | StrategyStopped(PartialRunRecord)
   | qualified operational noncompletion
```

Execution opens due scopes, evaluates each guard, and applies active effects in
occurrence order. At a prover decision it constructs the exact current
`ProverView`, invokes one strategy step, validates one move, and commits it
atomically. A capability request for a value outside the view refuses strategy
generation at that decision. At a Challenge it invokes the exact resolver. At
the first active terminal it records completion and stops.

`InterpretationFailed` is the completed typed-failure lane of the selected
challenge interpretation. It is not a Core terminal. `StrategyStopped` is not
a Core outcome and cannot be converted to Reject or Abort without an explicit
protocol event. Other missing capabilities, unsupported algorithms, resource
exhaustion, and checker defects follow K1's qualified noncompletion partition.

In particular, exhaustion of `ExecutionEvaluationControl.per_request_limits`
is `DeterministicLimitExceeded` and produces no semantic completion. It cannot
be relabeled as a Core rejection, strategy stop, or interpretation failure.

`CausalGenerationCapability` is a nonserializable, process-local capability
minted only by this invocation of `GenerateRun` after its restricted strategy
calls and terminal complete. It is bound to the live admitted-Protocol handle,
invocation handle, evaluator instance, and returned record object. It has no
canonical body, ID, receipt field, Boolean surrogate, or replay constructor and
expires with that process-local execution scope. A consumer requiring causal
generation must receive this capability directly; possession, serialization,
hashing, or successful replay of `RunRecord` never establishes provenance.

### 12.4 Run and replay records

```text
OccurrenceStatus = Inactive | Active

OccurrenceReceipt = {
  occurrence: OccurrenceRef,
  status: OccurrenceStatus,
  outputs: CanonicalSeq<CanonicalValue>
}

FreshChallengeReceipt = {
  challenge: ChallengeRef,
  law: ProtocolDeclarationRef<"pir.public-coin-law">,
  value: CanonicalValue<declared challenge type>
}

ChallengeResolverReceipt =
    Fresh(FreshChallengeReceipt)
  | FiatShamir(FSChallengeReceipt)

OracleReceipt =
    Published(occurrence, oracle,
              CanonicalValue<OraclePublicationOutputType(oracle)>)
  | Queried(occurrence, oracle,
            CanonicalValue<oracle.index_type>, visibility)
  | Answered(occurrence, oracle,
             CanonicalValue<OracleLookupResultType(oracle)>, visibility)

RunRecord = {
  protocol_id: ProtocolId,
  invocation_id: CoreInvocationId,
  occurrence_receipts: CanonicalSeq<OccurrenceReceipt>,
  challenge_receipts: CanonicalSeq<ChallengeResolverReceipt>,
  oracle_receipts: CanonicalSeq<OracleReceipt>,
  terminal: TerminalRef,
  terminal_public_outputs: CanonicalSeq<CanonicalValue>
}

PartialRunRecord = the exact prefix of RunRecord before a terminal

InterpretationFailureReceipt =
  FiatShamirSamplingFailure {
    construction: TranscriptConstructionId,
    receipt: FSSamplingFailureReceipt
  }

ProtocolFailureRecord = {
  protocol_id: ProtocolId,
  invocation_id: CoreInvocationId,
  occurrence_prefix: CanonicalSeq<OccurrenceReceipt>,
  challenge_receipts: CanonicalSeq<ChallengeResolverReceipt>,
  failure: exact typed interpretation DomainFailure,
  interpretation_receipt: InterpretationFailureReceipt
}

CompletedProtocolRecord =
    TerminalCompletion(RunRecord)
  | InterpretationFailure(ProtocolFailureRecord)
```

`FSChallengeReceipt` is closed by the companion page. Receipt output arity,
type, visibility, and effect-specific payload are derived from the exact Core;
a receipt cannot add an output or hide an expected one. The records are typed
execution data rather than independently authoritative subjects. Private
strategy state, witness, advice, randomness, and an opaque oracle body under
`PublicBinding` are absent. Exact replay receives any required confidential
oracle witness through a separate capability and checks every exposed answer.
A Plan-specific confidential generation record may bind private material
separately.
`PartialRunRecord` is diagnostic execution data for `StrategyStopped`, not a
completed Protocol record. K2 defines no affirmative prefix-replay result for
it; a later audit consumer needing one must define a distinct nonsemantic audit
relation and cannot call it `CheckedReplayMatch`.

K2 Fresh resolution has no completed semantic-failure row: unavailable or
failed fresh-coin supply is operational noncompletion. The sole
`InterpretationFailureReceipt` case is therefore the companion page's exact
sampling-failure receipt. Its `construction` must equal the construction named
by the admitted FS Protocol whose ID is `protocol_id`; the receipt's challenge,
prefix count, draw sequence, and states must recompute exactly under that
construction; the draw-sequence length must equal that challenge rule's
`maximum_draws`; and `failure` must be the construction's exact
sampling-exhausted coordinate and payload. These are closed typed runtime
fields, not a new identity-bearing or canonical transport schema. OIR or
Evidence must define any later serialization separately.

```text
ReplayRun(
  AdmittedProtocol,
  exact CoreInvocation,
  CompletedProtocolRecord,
  ExactOracleReplayCapabilities,
  ExactCheckAndExtensionCapabilities,
  ExecutionEvaluationControl)
  -> ReplayMatched(CheckedReplayMatch)
   | Refused(PIR.InteractiveCore, ReplayRecordMismatch)
   | qualified operational noncompletion
```

Replay consumes decisions and receipts in occurrence order, recomputes every
deterministic transition, challenge, check, oracle lookup, claim state, and
terminal output or typed interpretation failure, and requires equality of the
record variant plus exact exhaustion of all fields. Fresh replay consumes each
recorded `FreshChallengeReceipt.value` as the historical nondeterministic
choice, then validates its declared-law reference, canonical/domain membership,
schedule, conditions, and downstream effects; it makes no source, distribution,
or provenance claim and needs no replay source capability. FS replay instead
recomputes every challenge and sampling-failure receipt from the admitted
construction and never accepts a recorded challenge as a shortcut. A Fresh
Protocol cannot replay an interpretation-failure variant. Wrong variants,
coordinates, values, payloads, or unconsumed fields produce the named replay
refusal.

Replay does not invoke a strategy and therefore does not mint
`CausalGenerationCapability`. A trace can replay even when its producer had
future information. If a terminal run is separately accompanied by its still-
live `CausalGenerationCapability`, that capability attests only that this
semantic engine used the restricted generation relation for that one call;
successful replay never creates or strengthens it. Implementation isolation
and host side channels remain Evidence questions.

`CheckedReplayMatch` is a fresh opaque process-local capability minted only by
that successful `ReplayRun` call. It is bound to the live admitted-Protocol
handle, exact invocation handle, completed-record object, evaluator instance,
the exact Oracle and check/extension capability snapshots consumed by replay,
and that replay call's evaluation-control snapshot. It has no canonical body,
ID, receipt field, Boolean surrogate, copy constructor, or serialized form.
Supplying the same values, an equal record, or a prior replay report does not
recreate it. A consumer must receive the live matching capability directly;
one whose process scope has ended or whose operands differ is not a replay
match for that consumer.

`CheckedReplayMatch` is minted only when every K1 request completes under the
replay call's supplied evaluation control. Reusing the same evaluator and
limits from a completed generation, or limits componentwise sufficient for the
same deterministic requests, prevents a smaller replay budget from erasing a
shared completed transition. Insufficient replay limits yield
`DeterministicLimitExceeded`, not `ReplayMatched`, the record-mismatch refusal,
or a semantic Protocol outcome. A record by itself carries no evaluator-budget
or replay-match authority. Successful replay still does not mint or strengthen
`CausalGenerationCapability`.

## 13. PIR-owned source views

The names in this section denote exact owner schemas and owner operations, not
informal tuples or consumer-defined field lists. A downstream domain may select
a closed projection, but it cannot define a second PIR body schema, invent a
value, weaken a dependency closure, or mint source authority.

### 13.1 Common view schema, coordinates, and projection law

The exact Core-static view kinds are:

```text
CoreStaticViewKind =
    PublicBindingView
  | StrategyDecisionView
  | PublicCoinView
  | EffectView
  | ClaimReductionView
```

`ExecutionView` is deliberately not in that sum. Execution and replay depend
on the selected Challenge interpretation, so its owner coordinate is one exact
`ProtocolId`, even when two Protocols share a `CoreId`. The construction and
checked-result view kinds are defined in
[Fiat--Shamir](fiat-shamir.md#13-exact-source-view-contracts).

```text
PIRStaticViewOwnerCoordinate =
    CoreView(CoreId, CoreStaticViewKind)
  | ProtocolView(ProtocolId, ExecutionView)
  | ConstructionView(TranscriptConstructionId, ConstructionStaticViewKind)
  | FSResultView(CheckedFSConstructionResultRef, FSConstructionView)

PIRStaticViewCoordinate = {
  owner: PIRStaticViewOwnerCoordinate,
  semantic_language_profile_id:
    PIRInteractionProfileId | PIRTranscriptFSProfileId
}

StaticViewProfile(CoreView(_,_)) = PIRInteractionProfileId
StaticViewProfile(ProtocolView(FreshProtocolId,_)) = PIRInteractionProfileId
StaticViewProfile(ProtocolView(FSProtocolId,_)) = PIRTranscriptFSProfileId
StaticViewProfile(ConstructionView(_,_)) = PIRTranscriptFSProfileId
StaticViewProfile(FSResultView(_,_)) = PIRTranscriptFSProfileId

PIRViewPathStep =
    Field(field_ordinal)
  | VariantCase(case_ordinal)
  | SequenceElement(element_ordinal)

PIRViewAtomicBoundary =
    Unit | Natural | MetaBoolean | MetaSymbol | Bytes
  | ValueType | CanonicalValue(ValueType)
  | PIRReference | K1SemanticReference

PIRStaticViewFieldCoordinate = {
  view_coordinate: PIRStaticViewCoordinate,
  path: NonEmptyFiniteSeq<PIRViewPathStep>,
  boundary: PIRViewAtomicBoundary
}
```

Formation requires
`coordinate.semantic_language_profile_id = StaticViewProfile(coordinate.owner)`.
This field is part of the owner binding source body. In particular, an FS
`ExecutionView` cannot be wrapped under the Interaction profile merely because
its Protocol shares a Core with a Fresh Protocol.

A field coordinate forms only when its path reaches exactly one atomic leaf of
the closed body schema selected by `view_coordinate`; an absent field, interior
record, wrong sequence ordinal, wrong variant arm, or wrong boundary is
malformed. No text path, display name, wildcard, reflection callback, or
consumer extension is a coordinate.

The standalone PIR semantic profile governing the source coordinate fixes one closed
`PIRViewSchemaCatalog` in its inline profile-owned declaration catalog. For
each view kind it contains exactly the owner subject kind, body schema,
derivation law, field-coordinate resolver, required-read-closure law, source
binding schema, and capability contract. This is fixed evaluator dispatch
under the selected regime. It is not a declaration-module root in an effective
context, and the profile-import DAG remains the only generic closure mechanism;
it is also not a consumer-authored catalog.

```text
PIRStaticViewReadManifest =
  CanonicalNonEmptySortedUniqueSeq<PIRStaticViewFieldCoordinate>

RequiredPIRViewReadClosure(view_coordinate, selected_fields) =
  the least sorted-unique field set containing selected_fields and every
  owner-schema leaf needed to resolve its type, source coordinate, producer,
  scope/guard/order predecessor, and referenced semantic dependency

PIRStaticViewProjection = {
  coordinate: PIRStaticViewCoordinate,
  manifest: PIRStaticViewReadManifest,
  entries: CanonicalMap<PIRStaticViewFieldCoordinate, exact owner leaf value>
}
```

Every manifest field has the same `view_coordinate` and
`manifest = RequiredPIRViewReadClosure(coordinate, manifest)`. This fixed-point
equation is intentional: requesting a Check input, for example, also reads the
exact producer/type/schedule closure needed to interpret its `ValueRef`.
Requesting only the dangling ref does not form a smaller view. The realized
read set must equal the manifest exactly. Missing closure is
`MissingDependency`; extra, duplicate, aliased, reordered, or unconsumed
entries are `Malformed`. This equality closes both omission and phantom-read
directions.

### 13.2 Exact Core and Protocol view bodies

The five admitted-Core views and one admitted-Protocol view have these complete
bodies. Every sequence is in the corresponding admitted Core reference order;
every repeated type or backlink is owner-derived and checked rather than
authored.

```text
PublicBindingViewBody = {
  core_id: CoreId,
  scope_openings: CanonicalSeq<{
    scope_ref, parent, opening, complete_scope_path
  }>,
  bindings: CanonicalSeq<{
    binding_ref, scope_ref, class, value_ref, value_type,
    value_origin: InvocationPublicInput | Constant | DerivedValue |
                  OccurrenceOutput,
    complete_value_producer_coordinate
  }>
}

StrategyDecisionViewBody = {
  core_id: CoreId,
  decision_points: CanonicalSeq<{
    decision_ref, occurrence_ref, scope_ref, guard_ref,
    legal_move_type, prior_decision_refs
  }>,
  prover_view_formation: exact prefix/scope/guard visibility law,
  guaranteed_prover_reads:
    CanonicalMap<(ProverDecisionPointRef,ProverViewCoordinate),ValueType>,
  legal_move_types: CanonicalMap<ProverDecisionPointRef,ValueType>
}

PublicCoinViewBody = {
  core_id: CoreId,
  structural_public_coin_eligibility: MetaBoolean,
  verifier_private_dependency_closure:
    CanonicalSortedUniqueSeq<ValueRef>,
  challenges: CanonicalSeq<{
    challenge_ref, occurrence_ref, scope_ref, value_type, domain, fresh_law,
    correlation, reduction_use, public_conditions,
    complete_public_condition_producer_closure
  }>
}

EffectViewBody = {
  core_id: CoreId,
  occurrence_schedule: CanonicalSeq<{
    occurrence_ref, scope_ref, guard, effect, output_types
  }>,
  value_producer_graph: {
    public_inputs, verifier_private_inputs, constants, derived_values,
    occurrence_outputs, exact producer edges and ValueType at every node
  },
  messages: CanonicalSeq<exact Message declaration and occurrence backlink>,
  oracles: CanonicalSeq<exact Oracle lifecycle declaration/backlinks>,
  checks: CanonicalSeq<exact Check declaration and occurrence backlink>,
  terminals: CanonicalSeq<exact Terminal declaration and occurrence backlink>,
  supported_extensions: CanonicalSeq<exact admitted extension declaration>
}

ClaimReductionViewBody = {
  core_id: CoreId,
  claims: CanonicalSeq<{
    claim_ref, contract, usage, source, creation coordinate,
    complete consumer and terminal-disposition coordinates
  }>,
  reductions: CanonicalSeq<{
    reduction_ref, contract, scope, apply_occurrence, ordered inputs/outputs,
    side_inputs, required_challenges, complete publication requirements
  }>,
  terminal_dispositions:
    CanonicalSeq<(TerminalRef,ClaimRef,Consume | Discharge)>
}

ExecutionViewBody = {
  protocol_id: ProtocolId,
  core_id: CoreId,
  challenge_interpretation: ChallengeInterpretation,
  visible_history_law,
  resolver_coordinates,
  generated_execution_law,
  run_record_schema,
  replay_qualification_law,
  relation_run_view_issuance_law
}
```

For these view schemas, record field ordinals and variant tags are the written
order. A phrase of the form `exact X declaration` means the complete existing
Appendix-A `XBody`, not a new tuple with selected fields; each added backlink is
the unique admitted `OccurrenceRef` or producer coordinate derived by the Core
admission laws. `ValueType`, canonical values, Core references, K1 references,
and option/sequence/map wrappers use their already defined exact bodies. Thus
the catalog can enumerate every atomic leaf and the field resolver has no prose
or implementation-defined remainder.

`RequiredPIRViewReadClosure` is constructor-specific. In particular:

- a Public-binding leaf closes to its exact scope opening, type, origin, and
  producer coordinate;
- a decision/read leaf closes to the exact decision, visibility formation,
  type, and causal predecessor set;
- a Challenge leaf closes to its occurrence, public conditions, producer
  closure, law, correlation, and reduction-use fields;
- any Message, Check, Terminal, guard, or occurrence-output leaf closes through
  `occurrence_schedule` and `value_producer_graph` to every referenced producer,
  scope, guard, type, and ordering fact;
- a claim or reduction leaf closes to its exact creation/use/disposition and
  challenge/publication closure; and
- an Execution leaf closes to the exact `ProtocolId`, interpretation, and
  `CoreId`, so the Fresh and Fiat--Shamir Protocols over one Core cannot alias.

PIR owns these facts and this adequacy. Relations, Analysis, and OIR own any
additional proposition computed from them. A view is not a second Protocol
schema and adds no fact absent from its exact admitted owner body.

### 13.3 Issuance, bindings, capabilities, and outcomes

```text
PIRStaticViewIssueOutcome =
    Affirmative(IssuedPIRStaticView)
  | Unsupported(PIRStaticViewUnsupportedReason)
  | MissingDependency | KindMismatch | Malformed | Refused
  | DeterministicLimitExceeded | CheckerFailure

IssuePIRStaticView(
  exact admitted Core or Protocol selected by the coordinate,
  exact inert admitted-subject authority binding,
  matching fresh admission capability,
  exact PIRStaticViewReadManifest,
  exact PIR evaluator and deterministic limits)
    -> PIRStaticViewIssueOutcome

IssuedPIRStaticView = {
  projection: PIRStaticViewProjection,
  source_binding:
    ExactPIRStaticViewAuthorityBinding<view kind>
      = OwnerLocalSourceAuthorityBinding,
  capability: PIRStaticViewCapability<coordinate,manifest,projection>
}
```

The operation reauthenticates the owner body, resolves the catalog entry,
derives the full owner view, computes the least required closure independently
of the requested projection, and requires exact realized-read equality. It
constructs a K1 `OwnerLocalSourceAuthorityBinding` with owner `"pir"`,
capability family `"static-view"`, and the exact projection object as its local source
coordinate. Its profiled owner-binding payload commits to the producer
coordinate and complete field manifest. Its policy disposition is an explicit
`OwnerDefinesNoPolicy(exact PIR no-policy declaration ID)`; its policy-closure
ID commits to that
declaration and an `OwnerCapabilityRequirement` naming the exact typed consumer
and purpose. The binding is inert and contains no live token.

The fresh `PIRStaticViewCapability` retains that exact binding object, the
admitted handle, manifest and projection objects, evaluator, typed consumer and
purpose, and issuance occurrence. The local binding, capability, and issued
aggregate are noncopyable and nonserializable. Bearer delegation means passing
the identical live capability object; reconstruction, structural equality,
cross-family substitution, or reuse for another consumer or purpose grants no
authority.

The consumer and purpose intake coordinates may be any exact same-regime K1
`TypedContentId` owned by the downstream domain; PIR does not enumerate or
reinterpret downstream subject kinds. It nominalizes them before using them in
an authority identity:

```text
PIRSourceConsumerRoleId(family,c) =
  ProfiledSemanticId<"pir.source-consumer">(
    B, StaticViewProfile(coordinate.owner), {family, ContentRef(c)})

PIRSourcePurposeRoleId(family,p) =
  ProfiledSemanticId<"pir.source-purpose">(
    B, StaticViewProfile(coordinate.owner), {family, ContentRef(p)})
```

The payload and `OwnerCapabilityRequirement` contain these owner-profiled role
IDs, while the live capability retains the exact original `c` and `p` and
validation compares them exactly. This permits a typed OIR or Analysis
coordinate without teaching PIR that downstream language, yet prevents an
unrelated identifier, swapped role, different family, or different purpose
from substituting for the requested authority.

There is no semantic Negative: a static projection of an admitted owner either
is issued exactly or fails by one qualified noncompletion branch. An
unsupported view kind returns no partial projection or binding. A wrong Core,
Protocol, view kind, result origin, manifest, capability, or purpose is
`Refused` or `KindMismatch`, never a differently scoped affirmative.

### 13.4 Invocation-issued public setup view

Static `PublicBindingViewBody` declares public-binding meaning; it does not and
cannot contain an invocation's values. PIR exposes those values through one
separate fixed quotient:

```text
PublicSetupInvocationEntry = {
  binding_ref: BindingRef,
  scope_ref: ScopeRef,
  class: SessionContext | PublicParameter,
  value_type: ValueType,
  value: CanonicalValue<value_type>
}

PublicSetupInvocationViewBody = {
  protocol_id: ProtocolId,
  core_id: CoreId,
  entries:
    CanonicalSeq<PublicSetupInvocationEntry in BindingRef order>
}

PublicSetupInvocationViewId =
  ProfiledSemanticId<"pir.public-setup-invocation-view">(
    B, PIRPublicSetupProfileId, PublicSetupInvocationViewBody)

PublicSetupInvocationViewCoordinate =
  PublicSetupInvocationView(ProtocolId,PublicSetupInvocationViewId)

PublicSetupInvocationEntryBody(x) = R{
  0:N(x.binding_ref),
  1:N(x.scope_ref),
  2:V(0,Unit) | V(1,Unit), // SessionContext | PublicParameter
  3:ValueTypeBody(x.value_type),
  4:x.value.datum
}

PublicSetupInvocationViewBody(x) = R{
  0:ContentRef(x.protocol_id),
  1:ContentRef(x.core_id),
  2:S[PublicSetupInvocationEntryBody(e)... in BindingRef order]
}

IssuePublicSetupInvocationView(
  exact admitted Protocol,
  exact admitted CoreInvocation,
  exact inert Protocol and invocation authority bindings,
  matching fresh capabilities,
  exact PIR evaluator and limits)
    -> Affirmative({
         view,
         ExactPublicSetupInvocationViewAuthorityBinding
           = PortableSourceAuthorityBinding,
         PublicSetupInvocationViewCapability
       })
       | Unsupported | MissingDependency | KindMismatch | Malformed | Refused
       | DeterministicLimitExceeded | CheckerFailure
```

The entries are every and only `SessionContext` and `PublicParameter` binding
occurrence. The view contains no Statement, verifier-private input, unbound
public input, prover output, full `CoreInvocationId`, or completed record. Its
portable ID changes with any visible entry, type, binding coordinate,
`ProtocolId`, or `CoreId`; changing only a Statement or verifier-private value
does not change this quotient ID. This is the deliberate portable exception:
the K1 binding uses `PublicSetupInvocationViewId` as its portable source
coordinate, owner `"pir"`, family `"public-setup-invocation-view"`, and a
public-view-profiled payload, explicit no-policy declaration,
policy closure, and typed consumer/purpose requirement. The binding remains
inert. The fresh noncopyable capability retains that exact binding object and
the exact full invocation; substituting an equal or copied portable binding
does not move the live capability. Cold use must reauthenticate the Protocol
and invocation and rerun issuance; the portable body or binding alone grants
nothing.

### 13.5 Execution-issued relation grounding view

Relations sometimes needs the value that one exact verifier run consumed at a
scoped Statement, phase-input, Oracle, claim, reduction, check, terminal, or
public module-effect occurrence. `RunRecord` alone cannot supply that fact: it
does not retain every invocation value, and successful replay does not mint
causal provenance. PIR therefore owns one attenuated execution view rather
than requiring Relations to reconstruct a shadow Core state.

```text
RunBoundary =
    Initial
  | BeforeOccurrence(OccurrenceRef)
  | AfterOccurrence(OccurrenceRef)
  | Completion

RelationRunCoordinate =
    BindingValue(BindingRef)
  | OccurrenceOutput(OccurrenceRef, output_ordinal)
  | ChallengeValue(ChallengeRef)
  | OraclePublication(OracleRef, OccurrenceRef)
  | PublicOracleQuery(OracleRef, OccurrenceRef)
  | PublicOracleAnswer(OracleRef, OccurrenceRef)
  | ClaimHistory(ClaimRef, RunBoundary)
  | ReductionHistory(ReductionRef, RunBoundary)
  | CheckResult(CheckRef, OccurrenceRef)
  | TerminalResult(TerminalRef, OccurrenceRef)
  | PublicModuleObservation(OccurrenceRef, output_ordinal)

RelationRunReadManifest =
  FiniteOrderedUniqueSeq<RelationRunCoordinate>

RelationRunQualification =
    ReplayQualified
  | CausallyGenerated

RelationClaimCreation =
    NotCreated
  | InitialBindingCreated(BindingRef, RunBoundary)
  | ReductionOutputCreated(ReductionRef, OccurrenceRef, output_ordinal)

RelationClaimReductionUse = {
  reduction: ReductionRef,
  occurrence: OccurrenceRef
}

RelationTerminalDisposition = {
  terminal: TerminalRef,
  occurrence: OccurrenceRef,
  disposition: Consume | Discharge
}

RelationClaimHistory = {
  creation: RelationClaimCreation,
  reduction_uses:
    FiniteSeq<RelationClaimReductionUse in occurrence order>,
  terminal_disposition: None | Some(RelationTerminalDisposition)
}

RelationReductionHistory =
    PendingAtBoundary
  | OccurrenceNotReached
  | InactiveAt(OccurrenceRef)
  | AppliedAt {
      occurrence: OccurrenceRef,
      input_claims: CanonicalSeq<ClaimRef>,
      output_claims: CanonicalSeq<ClaimRef>
    }

RelationRunFact(c: RelationRunCoordinate) =
  the exact owner-derived typed payload selected by c:
    BindingValue             -> CanonicalValue<binding value type>
    OccurrenceOutput         -> CanonicalValue<exact output type>
    ChallengeValue           -> CanonicalValue<challenge value type>
    OraclePublication        -> CanonicalValue<publication output type>
    PublicOracleQuery        -> CanonicalValue<oracle index type>
    PublicOracleAnswer       -> CanonicalValue<oracle lookup-result type>
    ClaimHistory             -> RelationClaimHistory
    ReductionHistory         -> RelationReductionHistory
    CheckResult              -> MetaBooleanFalse | MetaBooleanTrue
    TerminalResult           ->
      (TerminalVerdict, CanonicalSeq<typed public outputs>)
    PublicModuleObservation  ->
      CanonicalValue<exact declaration-owned public output type>

RelationRunObservation<c> =
    Available(RelationRunFact(c))
  | Inactive
  | NotReached

RelationRunSelectedEntry<c> = {
  coordinate: c,
  scope_path: NonEmptySeq<ScopeRef>,
  observation: RelationRunObservation<c>
}

RelationRunView = {
  protocol_id: ProtocolId,
  qualification: RelationRunQualification,
  manifest: RelationRunReadManifest,
  entries: FiniteSeq<RelationRunSelectedEntry>
}

ScopeOpeningRunBoundary(Initially) = Initial
ScopeOpeningRunBoundary(BeforeOccurrence(o)) = BeforeOccurrence(o)

ChallengeOccurrence(core,c) =
  the unique admitted OccurrenceRef in core whose effect is Challenge(c)

RequiredBoundary(core,BindingValue(b)) =
  ScopeOpeningRunBoundary(
    core.scopes[core.bindings[b].scope].opening)
RequiredBoundary(core,OccurrenceOutput(o,_)) = AfterOccurrence(o)
RequiredBoundary(core,ChallengeValue(c)) =
  AfterOccurrence(ChallengeOccurrence(core,c))
RequiredBoundary(core,OraclePublication(_,o)) = AfterOccurrence(o)
RequiredBoundary(core,PublicOracleQuery(_,o)) = AfterOccurrence(o)
RequiredBoundary(core,PublicOracleAnswer(_,o)) = AfterOccurrence(o)
RequiredBoundary(core,ClaimHistory(_,boundary)) = boundary
RequiredBoundary(core,ReductionHistory(_,boundary)) = boundary
RequiredBoundary(core,CheckResult(_,o)) = AfterOccurrence(o)
RequiredBoundary(core,TerminalResult(_,o)) = AfterOccurrence(o)
RequiredBoundary(core,PublicModuleObservation(o,_)) = AfterOccurrence(o)
```

Within this owner-local grammar, `FiniteSeq` is a bounded process-local ordered
container, `NonEmptySeq` is its nonempty form, and
`FiniteOrderedUniqueSeq<T>` preserves the caller-supplied order while requiring
pairwise-distinct `T` values under exact typed structural equality. None of
these names imports K1 canonical ordering or encoding.

`RunBoundary` is the exact generated-run boundary order. `Initial` precedes the
first occurrence; each reached occurrence has a before boundary and, only when
its effect completes, an after boundary; `Completion` is the terminal or typed
interpretation-failure boundary. The boundary of a binding coordinate is the
deterministic opening boundary of its scope. The boundary of an occurrence
value is its `AfterOccurrence`; a history coordinate carries its requested
boundary explicitly. `RequiredBoundary` is total exactly over a statically
well-formed `RelationRunCoordinate`: every named reference, output ordinal,
effect kind, and owner must resolve in the admitted Core, and a binding's
resolved `ScopeOpening` must be one of the two closed alternatives above.
An absent, mismatched, or inapplicable owner-derived boundary makes the
coordinate malformed before disclosure is considered.

For a reached history boundary, `ClaimHistory` is always `Available`, even when
its creation is `NotCreated`. Its creation coordinate is the exact initial
binding opening or exact reduction-output occurrence from `ClaimSource`.
`reduction_uses` contains every active reduction through that boundary that
names the claim, including every use of a reusable claim. The optional terminal
entry retains the exact terminal and `Consume` versus `Discharge` disposition.
For a linear claim, admission permits at most one reduction use and no later
terminal disposition after that consuming use. For a reusable claim, reduction
uses do not close it; an exact terminal disposition does. Thus the history
determines liveness without collapsing reusable uses or the two terminal
dispositions. `ReductionHistory` likewise distinguishes a boundary before its
occurrence, completion before the occurrence, an inactive occurrence, and one
exact applied transition with its input and created output claims.

`Inactive` is legal only when the coordinate selects an occurrence-produced
fact, execution reached its before boundary, the scan deterministically
advanced past that occurrence without applying its effect, and that exact
occurrence guard was false. `NotReached` means the coordinate's required
boundary was not reached because an earlier terminal or interpretation failure
completed the record. Neither means that the owner failed to supply a requested
source.
Wrong-kind or out-of-range coordinates are malformed; absent required source
material, unsupported module semantics, and checker disagreement retain their
ordinary distinct qualified outcomes and produce no partial view.

The public whitelist is closed and dependency-sensitive. For this owner-local
view, define:

```text
PublicPCBasis(protocol,nodes) :=
  every node in nodes and in their transitive predecessor closure in
  PCGraph(protocol.core) has class StaticPublic or PublicHistory
```

`RunReachabilityBasis(protocol,record,boundary)` is the exact owner-derived set
of Section 11 nodes in `PCGraph(protocol.core)` whose realized outcomes in
`record` determine that execution reached `boundary`: the required
scope-opening path, every earlier terminal activity that had to be false, and,
at a completion boundary, the reached stopping terminal or FS
interpretation-failure control. For a stopping terminal the set includes its
occurrence activity/effect and `TerminalDecisionNode`; for an FS interpretation
failure it includes the Challenge activity/effect/output and the complete
public prefix/condition basis consumed by the admitted resolver. Formation
requires `record.protocol_id = protocol.id`; neither the ID nor ambient lookup
supplies the Core. This is a disclosure-only derived set; it adds no
schedule-prefix edge to `PCGraph`.

`RunFactBasis(protocol,record,c,fact)` is the exact realized-node set in
`PCGraph(protocol.core)`, under the same record/Protocol equality, selected by
coordinate:

1. `BindingValue(b)` selects `BindingObservationNode(b)`;
2. `OccurrenceOutput(o,n)` and `ChallengeValue` select the exact
   `OccurrenceActivityNode(o)`, `OccurrenceEffectNode(o)`, and
   `OccurrenceOutputNode(o,n)`;
3. an Oracle publication or answer selects those same applicable occurrence
   nodes, while a public Query additionally selects the exact producer of its
   index;
4. `ClaimHistory` selects `ClaimStateNode` plus every realized source,
   reduction-state, and terminal-disposition node represented through its
   boundary;
5. `ReductionHistory` selects `ReductionStateNode` plus the exact apply
   occurrence and claim-state nodes represented by its selected alternative;
6. `CheckResult` selects its invocation activity/effect/output nodes;
7. `TerminalResult` selects its activity/effect,
   `TerminalDecisionNode`, and every exact producer of its public outputs; and
8. `PublicModuleObservation` selects its occurrence activity/effect, exact
   declaration-owned module control/output nodes, and outward occurrence
   output.

The static coordinate shape must still be one of the previously named public
arms: a public binding; a both-party occurrence output; the unique Challenge
occurrence; an Oracle publication or exactly `Public` Query/Answer with matching
Oracle occurrence; a claim, reduction, or Check coordinate; a public terminal;
or an exact supported public module-output ordinal. Shape alone is never enough.

`PublicRelationRunObservation(protocol,record,c,observation)` holds exactly
under the following status law:

- `Available(fact)` requires both
  `PublicPCBasis(protocol,RunReachabilityBasis(protocol,record,RequiredBoundary(protocol.core,c)))`
  and
  `PublicPCBasis(protocol,RunFactBasis(protocol,record,c,fact))`;
- `Inactive` requires an occurrence-produced coordinate, public reachability to
  its before boundary, and a public basis for its complete scope path and
  `OccurrenceActivityNode`; the latter's predecessor closure includes every
  producer of the false guard, so a private false guard cannot be disclosed;
  and
- `NotReached` requires
  `PublicPCBasis(protocol,RunReachabilityBasis(protocol,record,Completion))`, where that exact
  reached completion precedes and prevents
  `RequiredBoundary(protocol.core,c)`. A stopping
  terminal or FS interpretation failure whose activity, decision, output,
  prefix, condition, or failure control depends on `VerifierPrivate` or
  `Invalid` state cannot be exposed even as absence.

The `InactiveAt` and `OccurrenceNotReached` alternatives nested inside a
reduction history, and a claim creation or use omitted because its source was
inactive or not reached, must pass the corresponding status law as part of
`RunFactBasis`; wrapping them in `Available` does not bypass it. Consequently,
both-party visibility of a Verifier output and a terminal's declared public
surface are insufficient by themselves: their effect/decision and output
producer closures must also be public. A Verifier-private input, Verifier-only
Oracle coordinate, verifier-only module output, opaque Oracle body, private
strategy value, internal transcript state, or any
`VerifierPrivate`/`Invalid` dependency cannot pass. These predicates belong to
PIR and have no caller-, Relations-, or policy-extensible arm.

`IssueRelationRunView` is a PIR owner operation. It receives one exact admitted
Protocol, the exact `CoreInvocation`, the identical completed-record object, an
ordered manifest, and either:

- the still-live matching `CausalGenerationCapability`, selecting
  `CausallyGenerated` for its exact terminal-completion record; or
- the fresh matching `CheckedReplayMatch` produced by `ReplayRun` over those
  exact operands, selecting `ReplayQualified`.

```text
IssueRelationRunView(...)
  -> Qualified<IssuedRelationRunView(
       RelationRunView,
       CheckedRelationRunViewAuthority)>
```

The operation first validates every coordinate's static shape, derives its
exact boundary, scope path, status, fact, reachability basis, and fact basis
from owner state, and then requires `PublicRelationRunObservation` for every
entry. It first requires the completed record's `protocol_id` to equal the
supplied `protocol.id` and its `invocation_id` to equal the supplied exact
invocation's ID; neither record ID is dereferenced as ambient authority.
Duplicate coordinates refuse. `entries` has exactly the manifest length and
order, and entry `i` names exactly manifest coordinate `i`; a permutation,
extra entry, omitted entry, equal value at another occurrence, or caller-created
fact cannot pass. The operation is atomic and returns no partial view.

It also returns fresh opaque `CheckedRelationRunViewAuthority` bound to the live
admitted-Protocol handle, exact invocation handle, completed-record object,
the supplied causal or replay-match capability, manifest object, and returned
view object. Those source operands remain in this authority; neither
`CoreInvocationId` nor the complete record is copied into the attenuated view.
The authority is nonserializable and expires with its process-local source
scope.

`RelationRunView`, its manifest, coordinates, histories, and selected entries
are owner-local typed structural objects. They have no K1 canonical body,
semantic ID, canonical-sort requirement, serialized authority, or Appendix A
encoding, and they enter neither `CoreId` nor `ProtocolId`. A copied tuple or
structurally equal value is not a view or authority. When the exact invocation
and every replay material are lawfully portable, cold replay may rerun
`ReplayRun` and this issuance operation to obtain a new typed view and fresh
authority; equality with a prior object grants nothing and never recreates
causal provenance. A durable consumer result must retain its portable source
coordinates and rerun the owner operation; it cannot embed this live view as
identity authority.

The view does not decode an external Interface container, inspect Plan-private
material, establish actor knowledge, or assert a relation proposition. A view
qualified `CausallyGenerated` may answer a question that explicitly requires
causality; `ReplayQualified` may not be widened to that role. Neither
qualification proves relation satisfaction, soundness, completeness,
knowledge, cryptographic security, or implementation isolation.

## 14. Composition and finite recurrence boundary

Canonical composition must produce a new `InteractiveCore` body, authenticate
it, and run all admission predicates again. Child occurrence paths are
represented by explicit scopes and the new total sequence. Public input,
value, claim, and terminal wiring must resolve to exact target references; no
ambient child handle remains in execution.

The new `CoreId` is the complete semantic composition context. Authoring
lineage, compiler route, and a composition-spec ID are excluded from challenge
meaning. If two routes normalize to the same exact Core body, replay between
them is intentional. An application needing domain separation supplies a
distinct identified SessionContext or static application domain.

V0 recurrence is finite unrolling before Core authentication. Recursive proof
verification is one finite message/check interaction or a supported exact-used
module effect; it does not recursively execute a child authority. Dynamic
schedules, unbounded loops, noncommunicating multiprover semantics, and
distributed-verifier knowledge require a future explicit extension and cannot
be encoded through labels or opaque effects.

## 15. Evidence boundary, nonclaims, and reopening conditions

The standalone
[K2 reference instrument](../../evaluation/k2-protocol-fiat-shamir/README.md)
provides bounded executable pressure for selected lifecycle, ordering,
strategy/replay, public-input binding, Oracle, claim, and refusal shapes. It
reuses K1 identity machinery, but its compact Python carrier is not the durable
Core carrier and does not execute every exact `AlgorithmUse`, capability,
`PCNode`/module-sink rule, generic Oracle type, or `PublicBinding` path defined
here. Its successful cases are finite inhabitance and falsification evidence,
not implementation conformance, capability nontransportability, protocol-family
coverage, or a cryptographic theorem.

This page establishes no cryptographic property, strategy implementation
conformance, distribution truth, relation satisfaction, endpoint coverage, or
production support. It does not claim that differently identified Cores are
observationally different, that a binding digest is collision resistant, or
that access receipts exclude host side channels.

The owner-local relation-run view exposes only the closed public coordinates in
Section 13.5. It supplies no verifier-private grounding channel. A later need to
ground a relation in confidential run state requires a separately designed
PIR-owned disclosure contract and purpose-specific view; a Relations manifest
cannot enable it. The derived decision references, structural read table,
replay-match capability, and relation-run view add no field to
`InteractiveCoreBody`, `ProtocolBody`, `CoreInvocationBody`, or any record body,
and therefore do not rotate `CoreId`, `ProtocolId`, or `CoreInvocationId`.

Reopen this Core if a K4 protocol requires one of the following without a
faithful finite supported extension:

- independent noncommunicating provers or distributed verifier knowledge;
- a statement introduced after the first challenge of its active scope;
- scheduler nondeterminism as protocol meaning;
- a necessary conditional-use implication outside the closed K2 syntactic
  `GuardImplies` law;
- an oracle whose publication/query/answer lifecycle cannot inhabit Section 7;
- a relation whose necessary run grounding is verifier-private and cannot use a
  separately authorized purpose-specific disclosure view;
- symbolic recurrence whose finite lowering is infeasible or semantically
  lossy; or
- an acceptance-relevant effect that cannot state exact transition,
  visibility, influence, replay, and bounds under the module law.

## Appendix A. Canonical bodies

All bodies below are exact `MetaValueV0` records. `R{...}`, `S[...]`, `V(tag,x)`,
`N(n)`, `Q(symbol)`, and `Y(bytes)` denote K1 record, sequence, variant,
natural, symbol, and bytes forms. References to ordinary IDs are
`Y(ContentRefV0(id))`; value types use `CanonicalValueTypeBody`; canonical
values use their admitted datum body. Fields are listed in ordinal order and
no other field is legal.

```text
InteractiveCoreBody(C) = R {
  0: S[ SemanticModuleRefBody(module) ... ],
  1: S[ PublicInputBody ... ],
  2: S[ VerifierPrivateInputBody ... ],
  3: S[ TypedConstantBody ... ],
  4: S[ DerivedValueBody ... ],
  5: S[ ScopeBody ... ],
  6: S[ PublicBindingBody ... ],
  7: S[ ChallengeBody ... ],
  8: S[ OracleBody ... ],
  9: S[ CheckBody ... ],
 10: S[ ClaimBody ... ],
 11: S[ ReductionBody ... ],
 12: S[ TerminalBody ... ],
 13: S[ OccurrenceBody ... ]
}

PublicInputBody(x) = R { 0: ValueTypeBody(x.value_type) }
VerifierPrivateInputBody(x) = R { 0: ValueTypeBody(x.value_type) }
TypedConstantBody(x) = R {
  0: ValueTypeBody(x.value_type), 1: x.value.datum
}

ValueRefBody =
  V(0,N(public_input_ref))
| V(1,N(verifier_private_input_ref))
| V(2,N(constant_ref))
| V(3,N(derived_value_ref))
| V(4,R{0:N(occurrence_ref),1:N(output_ordinal)})

DerivedValueBody(x) = R {
  0: ContentRef(x.algorithm),
  1: ContentRef(x.evaluation_contract),
  2: S[ ValueRefBody(input) ... ],
  3: ValueTypeBody(x.result_type)
}

ScopeOpeningBody = V(0,Unit) | V(1,N(occurrence_ref))
ScopeBody(x) = R {
  0: NoneOrSomeOrdinalBody(x.parent),
  1: ScopeOpeningBody(x.opening)
}

PublicBindingClassBody = V(0,Unit) | V(1,Unit) | V(2,Unit)
PublicBindingBody(x) = R {
  0: N(x.scope),
  1: PublicBindingClassBody(x.class),
  2: ValueRefBody(x.value)
}

CoinCorrelationBody =
  V(0,Unit)
| V(1,R{0:ModuleDeclarationRefBody(group),1:N(index),
        2:S[N(prior_challenge_ref)...]})

ReductionUsePolicyBody =
  V(0,Unit)
| V(1,ModuleDeclarationRefBody(sharing_contract))

ChallengeBody(x) = R {
  0: N(x.scope),
  1: ValueTypeBody(x.value_type),
  2: ModuleDeclarationRefBody(x.domain),
  3: ModuleDeclarationRefBody(x.fresh_law),
  4: CoinCorrelationBody(x.correlation),
  5: ReductionUsePolicyBody(x.reduction_use),
  6: S[ ValueRefBody(condition) ... ]
}

OraclePublicationModeBody =
  V(0,Unit)
| V(1,R{0:ValueTypeBody(binding_type),
        1:ModuleDeclarationRefBody(binding_contract),
        2:ContentRef(binding_algorithm),
        3:ContentRef(evaluation_contract)})

OracleBody(x) = R {
  0: N(x.scope),
  1: ValueTypeBody(x.index_type),
  2: ValueTypeBody(x.element_type),
  3: N(x.maximum_entries),
  4: OraclePublicationModeBody(x.publication_mode)
}

CheckBody(x) = R {
  0: ContentRef(x.algorithm),
  1: ContentRef(x.evaluation_contract),
  2: S[ ValueRefBody(input) ... ]
}

ClaimUsageBody = V(0,Unit) | V(1,Unit)
ClaimSourceBody =
  V(0,N(public_binding_ref))
| V(1,R{0:N(reduction_ref),1:N(output_ordinal)})

ClaimBody(x) = R {
  0: ModuleDeclarationRefBody(x.contract),
  1: N(x.scope),
  2: ClaimUsageBody(x.usage),
  3: ClaimSourceBody(x.source)
}

ReductionPublicationRequirementBody(x) = R {
  0: N(x.publication),
  1: NoneOrSomeOrdinalBody(x.next_challenge)
}

ReductionBody(x) = R {
  0: ModuleDeclarationRefBody(x.contract),
  1: N(x.scope),
  2: S[ N(claim_ref) ... ],
  3: S[ ValueRefBody(input) ... ],
  4: S[ N(challenge_ref) ... ],
  5: S[ ReductionPublicationRequirementBody(requirement) ... ],
  6: S[ ModuleDeclarationRefBody(output_claim_contract) ... ]
}

TerminalVerdictBody = V(0,Unit) | V(1,Unit) | V(2,Unit)
ClaimDispositionBody = V(0,Unit) | V(1,Unit)
TerminalBody(x) = R {
  0: TerminalVerdictBody(x.verdict),
  1: S[ ValueRefBody(output) ... ],
  2: S[ N(check_ref) ... ],
  3: S[ R{0:N(claim_ref),1:ClaimDispositionBody(disposition)} ... ]
}
```

The remaining exact bodies are:

```text
GuardBody =
  V(0,Unit)
| V(1,R{0:ContentRef(algorithm),
        1:ContentRef(evaluation_contract),
        2:S[ValueRefBody(input)...]})

ProverMessageBody(x) = R {
  0: ModuleDeclarationRefBody(x.channel),
  1: ValueTypeBody(x.payload_type)
}

VerifierMessageBody(x) = R {
  0: ModuleDeclarationRefBody(x.channel),
  1: ContentRef(x.algorithm),
  2: ContentRef(x.evaluation_contract),
  3: S[ValueRefBody(input)...],
  4: ValueTypeBody(x.payload_type)
}

OracleEffectBody =
  V(0,N(oracle_ref))
| V(1,R{0:N(oracle_ref),1:ValueRefBody(index),
        2:V(visibility_tag,Unit)})
| V(2,N(query_occurrence_ref))

ModuleEffectRefBody(x) = R {
  0: SemanticModuleRefBody(x.module),
  1: ModuleDeclarationRefBody(x.declaration),
  2: x.payload
}

CoreEffectBody =
  V(0,ProverMessageBody)
| V(1,VerifierMessageBody)
| V(2,N(challenge_ref))
| V(3,N(check_ref))
| V(4,N(reduction_ref))
| V(5,N(terminal_ref))
| V(6,OracleEffectBody)
| V(7,ModuleEffectRefBody)

OccurrenceBody(x) = R {
  0: N(x.scope), 1: GuardBody(x.guard), 2: CoreEffectBody(x.effect)
}

ChallengeInterpretationBody =
  V(0,Unit) | V(1,ContentRef(transcript_construction_id))

ProtocolBody(P) = R {
  0: ContentRef(P.core_id),
  1: ChallengeInterpretationBody(P.challenge_interpretation)
}

CoreInvocationBody(core_id, I) = R {
  0: ContentRef(core_id),
  1: S[ R{
       0:N(public_input_ref),
       1:CanonicalValueTypeBody(declared_type),
       2:value.datum} ... in PublicInputRef order ],
  2: S[ R{
       0:N(verifier_private_input_ref),
       1:CanonicalValueTypeBody(declared_type),
       2:value.datum} ... in VerifierPrivateInputRef order ]
}

PCNodeBody =
  V(0,N(public_input_ref))
| V(1,N(verifier_private_input_ref))
| V(2,N(constant_ref))
| V(3,N(derived_value_ref))
| V(4,N(scope_ref))
| V(5,N(binding_ref))
| V(6,N(occurrence_ref))
| V(7,N(occurrence_ref))
| V(8,R{0:N(occurrence_ref),1:N(output_ordinal)})
| V(9,N(claim_ref))
| V(10,N(reduction_ref))
| V(11,N(terminal_ref))
| V(12,R{0:N(occurrence_ref),1:N(control_ordinal)})
| V(13,R{0:N(occurrence_ref),1:N(output_ordinal)})
```

`NoneOrSomeOrdinalBody` is `V(0,Unit) | V(1,N(ordinal))`. Appendix shorthands
are exact:

```text
ContentRef(x)    = Y(ContentRefV0(x))
ValueTypeBody(T) = CanonicalValueTypeBody(T)
```

`ModuleDeclarationRefBody` and `SemanticModuleRefBody` are the exact Section 2
wrappers around the K1 union and content-reference carriers. None is a textual
identifier. Tag meanings are fixed by the order shown on this page. Changing a
field, tag, order, or admission law rotates the exact owning PIR profile and
every downstream profile that imports it. A module-owned declaration change
instead rotates that module and the subjects that exactly use it. The shared
Foundation semantic regime rotates only when a Foundation-owned mechanism or
its interpretation changes. Old bytes are never reinterpreted.
