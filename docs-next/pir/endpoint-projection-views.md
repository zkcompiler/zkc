# Endpoint Projection Views

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative K3-D target
> **Provisional owner:** `pir`
> **Authority:** This page defines the PIR-owned source side of the bounded
> K3-D endpoint-projection contract. It has no authority over the current
> specifications under [`docs/`](../../docs/README.md), does not activate full
> Stage 4B, and makes no implementation or cryptographic-security claim.

## 1. Boundary

OIR projection is a relation between exact source meaning and exact target
meaning. It is not a producer-selected list of facts. PIR therefore derives a
closed purpose-specific quotient before OIR construction begins:

```text
ClassifyEndpointProjectionSupport(exact admitted sources, purpose, profile)
  -> SupportedExtractionBasis | Unsupported | qualified noncompletion

ExtractEndpointSourceView(SupportedExtractionBasis, exact PIR evaluator)
  -> CheckedEndpointSourceView | qualified noncompletion
```

The quotient body excludes whole source-subject provenance. Its live checked
capability retains the exact Protocol, Interface, optional Plan and
`CheckedPlanRealizes`, read manifest, realized read receipts, and private
source-to-view rebase maps. A serialized body transfers none of that
authority.

This exclusion has one important limit. An original K2 ordinal or content ID
that K2 itself places into transcript bytes, a challenge namespace, or another
runtime semantic operation remains an ordinary semantic operand. Removing it
would change protocol meaning. Ordinary Interface, claim, codec, and Plan
ordinals are instead rebased into view-local graph references.

PIR owns source completeness. OIR owns target meaning. The projection checker
owns neither and validates the relation externally.

## 2. Purpose and bounded support

```text
EndpointRole = Verifier | Prover
ChallengeMode = Fresh | FiatShamir

EndpointProjectionPurpose =
    VerifierEndpoint(ChallengeMode)
  | GenericProverEndpoint(ChallengeMode)
  | PlanSpecializedProverEndpoint(ChallengeMode)
```

`K3DProjectionV0` supports exactly:

- `VerifierEndpoint(FiatShamir)`; and
- `PlanSpecializedProverEndpoint(FiatShamir)` over the base K2 effects and
  base K3-B Plan grammar.

It recognizes but returns early typed `Unsupported`, with no partial view,
OIR, or proposition, for Fresh endpoints, generic Plan-free Provers, a Core
with any native Oracle declaration or occurrence, an admitted module effect
of any kind. A legacy module carrier without a supported K2
effect contract stops earlier at PIR admission and never reaches this
classifier. A future Interface or Plan grammar containing module recipes has a
different semantic regime and fails the selected regime/profile join before
this classifier; current K3-D does not authenticate a foreign grammar merely
to return a feature label.

The support result is affirmative authority. A support-marked case cannot
later escape through `Unsupported`; disagreement by the selected evaluator is
`CheckerFailure`.

The semantic payloads are closed:

```text
EndpointUnsupportedReasonBody =
    V(0,U) | V(1,U) | V(2,U) | V(3,U)
// FreshEndpoint | GenericProverEndpoint
// StandardOracleEndpoint | ModuleEffectEndpoint

EndpointUnsupportedBody =
  S[EndpointUnsupportedReasonBody... in increasing tag order, nonempty]

EndpointSupportOutcomeBody =
    V(0,U) | V(1,EndpointUnsupportedBody)
  | V(2,U) | V(3,U) | V(4,U) | V(5,U) | V(6,U) | V(7,U)
// Supported | Unsupported | MissingDependency | KindMismatch | Malformed
// Refused | DeterministicLimitExceeded | CheckerFailure

EndpointExtractionOutcomeBody =
    V(0,U) | V(1,U) | V(2,U) | V(3,U)
  | V(4,U) | V(5,U) | V(6,U)
// Affirmative | MissingDependency | KindMismatch | Malformed | Refused
// DeterministicLimitExceeded | CheckerFailure
```

`Unsupported` carries every and only applicable supported-grammar reason and
returns no extraction basis; a Core containing both Oracle and a
module effect therefore has two reasons, not an unspecified first error.
Because no source-adequacy proposition is formed at this boundary, extraction
has no semantic `Negative`. A missing source is `MissingDependency`; a formed
owner carrier that fails the selected adequacy/profile law is `Refused`; and a
contradiction after affirmative owner admission is `CheckerFailure`. Wrong
edge shape remains Interface nonadmission, and a missing Plan join prevents
request formation. Recursive diagnostics are non-authoritative. Only the
later exact source/target projection proposition has a semantic Negative arm.

## 3. Exact owner read manifest

For each supported purpose, PIR defines a total disposition over the exact
identity-bearing schemas of `ProtocolBody`, `InteractiveCoreBody`,
`TranscriptConstructionBody`, `ProtocolInterfaceBody`, and optional
`ProverPlanBody`:

```text
EndpointReadDisposition =
    ProjectionRelevant(nonempty sorted-unique view_sinks)
  | SourceJoinOnly(join_axis)
  | InertForPurpose(reason)
  | UnsupportedByK3D(reason)
```

The manifest is profile-owned, never producer-authored:

```text
EndpointOwnerSchemaSetId =
  ProfiledSemanticId<"pir.endpoint-owner-schema-set">(
    B, PirEndpointSourceViewProfileId,
    EndpointOwnerSchemaSetDomainBody)

EndpointReadManifestId(purpose) =
  ProfiledSemanticId<"pir.endpoint-read-manifest">(
    B, PirEndpointSourceViewProfileId,
    EndpointReadManifestDomainBody(purpose))
```

The manifest covers owner identity-body reads. Exact dependency-preimage reads
are a second, nonoptional closure rather than hidden exceptions to that
manifest:

```text
ResolveEndpointDependencyClosure(
  selected owner receipts,
  exact admitted K1/K2/K3-B dependencies,
  selected K1 dependency evaluator)
    -> CheckedEndpointDependencyReadClosure
```

It follows every selected content and declaration reference, authenticates its
exact preimage, derives the sorted `exact_used_dependencies` table, and records
one receipt for every preimage field used to obtain types, algorithm/evaluation
contracts, module declarations, failure declarations, or General-codec laws.
The K3-B Interface capability separately establishes its General-codec law
evidence; extraction consumes that admitted capability and cannot recreate the
evidence from a declaration ref. Missing, extra, or unused dependency receipts
fail extraction. Consequently, `actual read set equality` below means equality
of both the owner-manifest receipts and this fixed dependency closure, not only
the five root bodies.

The owner-schema set imports the exact five-root grammar under the pinned
semantic regime. One fixed exhaustive traversal law and one fixed
purpose-specific disposition law own all coordinates. They are not serialized
grammar/rule DAGs and cannot be producer-edited. Appendix B closes their tags,
atomic coordinates, root optionality, policy, receipts, and selector
subroutines.

`K3DProjectionV0` accepts only the selected v0 `SemanticRegimeId`
`a36c5cc0d431a16bd6e96e933101e8f2d20ad5f4f3a770327ddb6362f071203c`
and its exact K1 `SemanticLanguageProfileId` import chain:

```text
PIRInterfacePlanProfileId
  <- OirEndpointGraphProfileId
  <- PirEndpointSourceViewProfileId
  <- OirProjectionRelationProfileId
  <- OirProjectionValidationProfileId
```

The target requires each arrow to be one exact-used `profile_imports` edge to
the immediate semantic dependency, not an ambient bundle hash or a textual
version label. The bounded executable baseline exercises that topology with
the following profile-ID digests under the selected regime, in the same order:
`3249d35408bd507c6613eb2d7496b95c6d3313a85bac41f28751d1957d6e4f8c`,
`6138f0ffe95880b2cfe0a4ccd3da71610974193a2fcf6aaa60ae3cf7bfacdfa4`,
`ccb080314d48881cf89d8b59bc3d14364311797b49f2048b31fd59e684fbaaa7`,
`cf79a520db90374e7c1bbed17cda79c20130e479a538de9c8a41826b62a60330`,
and `b183c8af6fad580b0c4d003f4b4e3c26e08fca63dff0b6cf36f6b210091a89fd`.
The identity equations below consume full typed profile IDs, never bare digest
strings. These values are an executable-only post-K3-E-repair snapshot, not
durable selected constants. They do not supply the complete canonical
`SemanticLanguageProfileBody` preimages or establish durable owner-profile byte
parity. Until those complete owner profile preimages are published, this page
fixes the ideal target equations and import topology, not independently
reconstructible profile IDs.

The owner-schema-set and read-manifest IDs are formed under the exact source-
view profile. A same-shaped future regime or profile does not inherit this
policy. A change to Interface/Plan meaning rotates the endpoint graph and all
four K3-D descendants; a source-view change rotates source, projection, and
validation; a projection change rotates projection and validation; and a
validation-only change rotates only validation. A Relations-only K3-B profile
change remains outside this exact Interface/Plan-rooted profile closure and
therefore does not rotate the K3-D chain. There is no wildcard, default,
authored callback, textual reason, or precedence rule. Missing, extra, or
unknown schema edges fail before extraction.

The four closed sequence selectors are owner algorithms:

```text
AllElements
K2RoleSemanticClosure
K3BInterfaceEndpointClosure
K3BPlanReachableClosure
```

Each returns a total selected/complement partition, canonical traversal,
realized read receipts, and private rebase maps. Relevant receipts must equal
the view constructor's actual read set, and each receipt declares every graph
table to which the exact owner subtree may contribute. One subtree may feed
several tables; for example, a selected check feeds dependency, type, and
spine construction. Join-only material may bind only the live
extraction/validation capability. Inert material cannot enter quotient tables
by a direct read. This does not erase an indirect K2 commitment: the complete
Core and Construction preimages still determine retained IDs that K2 absorbs
or uses in challenge namespaces. Plan keys and dead Interface/Plan elements
can be genuinely quotient-inert because their whole owner IDs are not
retained. An unsupported concrete element stops classification before any
view is produced.

### 3.1 Live owner adapter and bounded supplement

Reading an admitted root body is not by itself owner authority. Before source
extraction, bounded K3-D must join the exact live capabilities issued by the
owners for every fact family that those owners currently expose:

- K2 `PublicBinding`, `PublicCoin`, `Effect`, and `ClaimReduction` views, plus
  `StrategyDecision` for a Plan-specialized Prover;
- K2 `TranscriptDeclaration`, `RequiredInfluence`, and
  `ChallengeTransition` views;
- one exact checked FS-construction authority and its `FSConstruction` view;
- one K3-B `ProtocolInterface` correspondence view over the complete selected
  invocation, Statement, transport, slot, and transitive-codec closure; and
- for the Prover, one affirmative `CheckedPlanRealizes` result over the exact
  Protocol and Plan.

Each transferable binding is the owner's exact K1 source-authority envelope.
Each consumed capability is a live, identical bearer and names the same typed
K3-D consumer and the source- and role-specific projection purpose. A copied,
reconstructed, wrong-purpose, wrong-consumer, stale-source, or partial view is
not equivalent authority even when its public fields compare equal.

The current executable owners do not yet issue all rich source facts selected
by Sections 5--10. The bounded evaluation may bridge only that availability
gap with `FutureOwnerSupplementV0`. Its identity commits to the exact Core,
Construction, Protocol, Interface, optional Plan, purpose, and complete
supplement body under the source-view language profile. A preparatory
owner-side operation may form its binding and a provisional bearer after
closed-shape and root-level validation, but that bearer is inert: it is not
live authority and no graph constructor may consume it. Activation must first
validate exact equality with every overlapping live owner view and the exact
checked Plan. Only that complete join may make the identical bearer live and
mint:

1. an exact K1 `PortableSourceAuthorityBinding` whose operation policy is the
   explicit owner-no-additional-policy case;
2. a typed capability requirement for the K3-D consumer and exact projection
   purpose; and
3. one process-local, noncopyable, nonserializable identical-bearer
   capability.

Every keyed closed table is checked for exact cardinality and uniqueness at
this boundary: claims, reductions, challenges, Statement aliases, transports,
completions, Plan recipes, and Plan exports may neither collapse duplicate
keys nor smuggle extras. Claim overlap includes the complete origin tuple
`(scope, Binding | ReductionOutput, source name, output ordinal)`, derived
from the owner-issued public-binding and claim/reduction views; matching only
claim names and reduction arities is insufficient.

The raw supplement carrier is inert. Only the following residual families may
come from its admitted capability in bounded v0: rich claim/reduction contract
and terminal detail; FS state/scalar types, algorithm/evaluation ABIs, and
per-challenge laws; structural codec/type-tree laws, fibres,
public-derivation transports, and completions; and rich Plan
recipe/evaluation/export detail. Core occurrence, binding, challenge,
claim/reduction-use, Interface coordinate/codec/Statement/transport, and Plan
route facts already exposed by owner views must agree exactly and cannot be
overridden by the supplement.

`CheckedProjectionOwnerAdapterV0` is minted only after that join. It retains
the exact request, purpose, all live owner views, checked FS authority,
optional checked Plan, admitted supplement capability, and the closed
supplement-only path set. Extraction and independent target construction may
consume only this adapter, never a raw supplement or unauthenticated root.
Absent required authority is `MissingDependency`; a formed but stale or
disagreeing authority is `Refused`; contradiction after the complete join is
`CheckerFailure`.

This mechanism authenticates one selected bounded supplement law. It is not a
claim that K2/K3-B already expose the universal future owner-view surface.
When an owner adds a live view for a residual family, the corresponding path
must leave the supplement and join that view; overlapping independent truths
are forbidden.

## 4. One source quotient, several owner components

The exact quotient contains one OIR-owned endpoint semantic graph. OIR owns
the bridge value schema and `DeriveEndpointContractV0`; PIR owns the exhaustive
source traversal and constructs that exact foreign-owned value without a
shadow definition. A schema or contract-law change rotates the OIR language
profile and this exact-used PIR projection-view profile. Producing the value
transfers no source authority.

```text
EndpointSourceView = {
  profile,
  purpose,
  semantic_graph: EndpointSemanticGraph
}

EndpointSemanticGraph = {
  role,
  exact_used_dependencies,
  value_types,
  constants,
  pure_nodes,
  role_abi_graph,
  endpoint_spine,
  static_fs_semantics,
  claims,
  anchored_obligations,
  optional_plan_graph
}
```

Static obligations, requirements, and the completion interface are not three
more authored tables. The fixed `DeriveEndpointContractV0` law in Section 7
derives them uniquely from this graph. This avoids two semantic copies of the
same action while retaining an exact static conformance and requirement
boundary for OIR and Realization.

The Protocol component consumes and rechecks the same exact fact families
exported by K2
`PublicBindingView`,
`StrategyDecisionView`, `EffectView`, and `ClaimReductionView`,
and the FS `TranscriptDeclarationView`, `RequiredInfluenceView`,
`ChallengeTransitionView`, and `FSConstructionView`. The Interface component
is the role-filtered, transitive K3-B codec/slot graph. Appendix B's exhaustive
five-root traversal defines completeness and disposition, while Section 3.1's
live views provide owner authority for every currently issued overlap; neither
can substitute for the other. Residual selected facts are admitted only by the
bounded supplement capability. The Plan component is
the reachable K3-B Plan graph after affirmative `PlanRealizes` over the same
exact Protocol and Plan.

Extraction reads no K3-C Analysis judgment, theorem, experiment, relation
subject, runtime trace, source location, carrier label, compiler route, or
Realization choice.

## 5. Value graph and endpoint spine

`EndpointDependenciesV0` is the sorted-unique direct graph-dependency index of
every and only retained Core, Construction, Algorithm, EvaluationContract,
and SemanticModule ref. The live `CheckedEndpointDependencyReadClosure`
separately follows those preimages recursively through exact
SemanticPrimitiveRef pairs, module imports, declarations, failures, and
General-codec laws. Those authenticated transitive reads remain in the live
dependency ledger; an ID from a kind absent in `EndpointDependencyBody` is not
silently inserted into graph identity.

`EndpointValueTypesV0` is the sorted-unique least closure of every type
named by retained invocation, value, action, anchor, Plan, codec, portable
operation, and FS-construction fields, including K1 Boolean and every resolved
algorithm ABI port. Formation rejects an unused table member, a missing
member, or an out-of-range type/dependency ref. Both tables sort by full
canonical body bytes; neither is caller-selected.

Constants retain an exact type and datum and preserve filtered
ascending original K2 `ConstantRef` order. Pure nodes retain exact
portable algorithm/evaluation dependencies, ordered inputs, and result type.
They preserve filtered ascending original K2 `DerivedValueRef` order, which is
already dependency-before-use, and include every reachable K2 `DerivedValue`;
equal values do not merge source nodes. The role ABI preserves the filtered
K3-B table orders defined in Section 8.

Source-side `ProverEndpointValueClosure` starts from every original value ref in
the Prover graph's local and counterparty base actions, guards, FS laws,
anchors, Plan view reads, and retained pure nodes, then follows every producer
to primitive leaves while the private rebase maps are still available. Every
invocation-input leaf must be a public target; typed constant leaves remain
valid static-public leaves. Every selected original public-computation node
must have K2 class `StaticPublic` or `PublicHistory`, and the complete original
predecessor set must be a subset of K2's admitted `PublicCoinView` predecessor
closure. This is already entailed by an admitted FS Core because Verifier
messages, Checks, guards, challenge conditions, reductions, and terminals are
K2 public-coin sinks, but extraction reruns it before discarding the maps. A
verifier-private leaf contradicts the live admitted FS/PublicCoinView basis and
is `CheckerFailure`; it does not add a private Prover ABI slot.

OIR cannot replay source-ordinal membership after rebasing. The shared bridge
profile therefore also defines a source-independent `EndpointPublicClosureV0`
over the canonical graph: a Public invocation target and typed constant are
`StaticPublic`; a pure node, guard, deterministic Verifier message, Check,
reduction, or terminal joins its graph predecessors; and Prover messages,
challenges, and public presentations use the corresponding fixed K2 transfer
class. Local OIR admission requires every retained Prover root and predecessor
to classify `StaticPublic` or `PublicHistory` and forbids a retained
`VerifierPrivateInput` target. Exact graph equality transfers this endpoint-
local result back to the source-qualified closure; it does not recreate the
discarded source map. Here a Prover root means an `EndpointValueRef` demanded
by base/FS/anchor computation or the endpoint-value side of a Plan view read.
It excludes `PlanValueRef` private material, randomness, state, and recipe
intermediates, which are governed by Plan admission. A value retained solely
inside a counterparty action is descriptive and grants neither local
observation nor evaluator authority.

The endpoint spine is a single total semantic order. Each occurrence carries
its exact endpoint action rather than a kind tag plus a second effect table:

```text
SourceSpineEvent =
    FsInitialization
  | ScopeOpening {
      k2_scope_path,
      parent_scope_event,
      Initially | BeforeOccurrence(k2_occurrence_ordinal)
    }
  | PublicBinding {
      k2_binding_ordinal,
      scope_event,
      class,
      value
    }
  | CoreOccurrence {
      k2_occurrence_ordinal,
      scope_event,
      Always | Guarded(algorithm, evaluation, inputs),
      ProverMessage(channel, payload_type)
        | VerifierMessage(channel, algorithm, evaluation, inputs,
                          result_type)
        | Challenge(challenge_law)
        | Check(algorithm, evaluation, inputs, Boolean result_type)
        | Reduction(reduction_anchor)
        | Terminal(terminal_anchor)
    }
```

Sequence position is the local `SourceSpineEventRef`. Scope and binding events
are inserted at their exact owner-derived K2 boundaries before affected
occurrences. The activity law includes scope ancestry/opening, guard
evaluation, and suppression after an earlier terminal or FS interpretation
failure. Action ownership is derived from role and action kind: messages are
local to their source role and counterparty obligations for the other role;
challenges are local public derivations in both roles; checks, reductions, and
terminals are Verifier-local and Prover-counterparty. Neither ownership nor
the stopping law is stored as an authored field.

The original scope-path, binding, and occurrence naturals are retained only
where K2 uses those numbers in exact transcript semantics. Graph edges always
use local refs. Bounded v0 preserves the total spine order. Any future
reordering needs a new relation profile with a checked commutation catalog.

## 6. Static Fiat--Shamir semantics

The source view retains the exact construction state/bytes/natural types,
initial state, absorb/squeeze/advance algorithms and contracts, application
domain, sampling-failure type, challenge rules, K2 frame law, exact derived
prefix law, and exact retry/state-advance law. The per-draw namespace recipe is
derived from those fields plus the challenge action's exact spine scope and
original K2 coordinate; it is not stored a second time. Runtime values and
receipts do not enter identity. Challenge laws preserve ascending original K2
`ChallengeRef` order.

K2 framing distinguishes graph refs from semantic frame coordinates:

```text
K2FrameCoordinate =
    ScopePath(S[N(original ScopeRef)...])
  | Binding(N(original BindingRef))
  | Occurrence(N(original OccurrenceRef))
  | ChallengeInput(N(original ChallengeRef), N(input_ordinal))
```

The fixed K2 frame law combines those exact naturals with the referenced
action, guard, runtime activity, and endpoint values. Every later runtime
instantiation must derive byte-for-byte the K2 `FrameBody`, then
`M(FrameBody)`. The K3-D static contract names that exact recipe; it never
substitutes a view-local ABI, spine, or challenge-law ordinal for a K2 ordinal.

Challenge namespace is a recipe, not one stored namespace value:

```text
ChallengeNamespaceRecipe(T,c) = {
  construction dependency,
  Core dependency,
  exact root-to-c K2 scope path,
  exact K2 ChallengeRef,
  domain,
  value type,
  correlation
}

EvaluateNamespace(recipe, draw_ordinal i) =
  admit at TranscriptBytesType(O(M(R {
    0: ContentRefV0(T.id),
    1: ContentRefV0(T.core_id),
    2: exact scope path,
    3: N(c),
    4: domain,
    5: value type,
    6: correlation,
    7: N(i)
  })))
```

Each retry therefore obtains a distinct namespace and advances state before
acceptance exactly as K2 requires. No namespace datum, draw, sampled value,
attempt count, proof byte string, or receipt is stored in source-view or OIR
identity.

Static-FS formation is a total bijection: every Challenge action names exactly
one challenge-law entry, every entry is named once, and original
`ChallengeRef` ordinals are unique and in ascending order. The action output
type, exact root-to-scope path, domain, value type, correlation and earlier
joint members, conditions, draw bounds, algorithm ABIs, and the one
construction-wide failure must agree with the admitted K2 owners. The fixed
law executes over the admitted graph plus its authenticated resolved
dependency environment, not graph bytes alone; missing algorithm, evaluation,
failure, or General-codec preimages prevent derivation/admission.

## 7. Derived static endpoint contract, claims, and requirements

`DeriveEndpointContractV0` is the one profile-owned expansion law. Its input is
the complete formed graph plus the authenticated dependency environment; its
output is one closed, non-identity result:

```text
DerivedEndpointContract = {
  static_obligations,
  requirements,
  completion_interface
}
```

None of these fields is an additional OIR identity field. Source extraction
and local OIR admission independently derive the complete result. An
implementation may cache it only with the exact admitted graph, dependency
environment, evaluator, and profile that produced it.

This contract is deliberately static. It says which semantic operations,
presentations, counterparties, and resources a conforming endpoint must
realize, and imports their exact source laws. It is not an execution trace or
a second operational semantics. In particular it does not choose a schedule,
name runtime values, number draw attempts, version state, decide guarded
presence, package transport bytes, or manufacture a runtime endpoint result.
Those path-dependent subjects belong to Stage 4B. Keeping them out of K3-D
avoids inventing path-sensitive state joins and wire laws before their owning
execution model exists. It does not weaken Fiat–Shamir preservation: the
complete K2 framing, prefix, transition, retry, decode, and global-failure laws
remain in the identity-bearing graph and in exact projection equality.

### 7.1 Closed static-obligation index

The static-obligation index is generated by one fixed law. It is neither an
authored action table nor an execution order:

```text
EndpointFrameRecipeBody =
    V(0,U) | V(1,U) | V(2,U)
  | V(3,N(scope_spine_ref))
  | V(4,N(binding_spine_ref))
  | V(5,N(guarded_spine_ref))
  | V(6,N(message_spine_ref))
  | V(7,N(message_spine_ref))
  | V(8,R{0:N(challenge_spine_ref),1:N(input_ordinal)})
// CoreHeader | ConstructionHeader | ApplicationDomain | ScopeOpening
// PublicBinding | GuardOutcome | ProverMessage | VerifierMessage
// ChallengeCondition

EndpointPresentationCoordinateBody =
    V(0,N(slot_ref))
  | V(1,N(statement_alias_ref))
  | V(2,N(transport_edge_ref))
  | V(3,N(completion_ref))
  | V(4,R{0:N(completion_ref),1:N(coordinate_ordinal)})
// ExternalSupply | Statement | Transport | CompletionTag
// CompletionPayload

CodecDirectionBody = V(0,U) | V(1,U)
// Encode | Decode

EndpointStaticObligationBody =
    V(0,N(slot_ref))
  | V(1,N(decision_spine_ref))
  | V(2,EndpointFrameRecipeBody)
  | V(3,N(spine_ref))
  | V(4,R{0:N(challenge_spine_ref),1:N(challenge_law_ref)})
  | V(5,R{0:CodecDirectionBody,
          1:EndpointPresentationCoordinateBody})
// SlotIngress | PlanDecision | K2Frame | LocalOccurrence
// ChallengeInterpret | Presentation
```

`SlotIngress` occurs once for every selected external-supply slot. Invocation
fibres and `SuppliesInvocation` Statement aliases share that one ingress; they
never create duplicate decoding authority.

`PlanDecision` occurs once for each retained Prover-message move entry in a
Plan-specialized Prover graph. It imports the exact reachable Plan decision:
view reads, private material, randomness availability, state row, recipe DAG,
move, and total selected-state update row. The obligation does not prescribe
a concrete supplier, entropy source, storage device, or guarded runtime state
merge.

`K2Frame` occurs for Core, Construction, and application-domain initialization
when FS semantics is present; for every selected scope opening, public
binding, guarded occurrence, Prover message, Verifier message, and challenge
condition required by the exact K2 prefix law; and in the fixed K2 order. Each
recipe resolves the original ordinals retained by the spine and challenge
law, derives the exact K2 `FrameBody`, and imports immediate absorption under
the selected construction. It therefore cannot substitute view-local
ordinals, omit an inactive guard outcome, or let an implementation choose
which messages enter a later challenge prefix.

`LocalOccurrence` occurs for a Prover message in the Prover endpoint; for a
deterministic Verifier message, Check, Reduction, or Terminal in the Verifier
endpoint; and for no counterparty-only occurrence. Its action body or unique
anchor is the exact semantic law. FS Challenge actions are represented by
`ChallengeInterpret` instead of a second local-occurrence row.

`ChallengeInterpret` occurs exactly once for every Challenge action/law
bijection in each FS endpoint. It imports the complete construction-global K2
transition: exact prefix, per-draw namespace, squeeze-length check, state
advance before acceptance, acceptance, retry bound, decode, correlation, and
the one shared sampling-exhausted failure. The static row is not a claim that
one draw, or any fixed number of draws, occurs at runtime.

`Presentation` is derived from the complete role ABI by this total direction
law: `ExternalSupply` is Decode; `ExposesOpenedBinding` is Encode;
`SuppliesInvocation` adds no row; a transport from this role to itself yields
Encode and Decode, from this role to another destination yields Encode, and
from another role to this role yields Decode; a selected `PublicDerivation`
to this role or to the application export owner is Encode-only and never an
input; and every completion tag or payload is Encode. One obligation is
generated for each resulting direction. Every Verifier completion variant
contributes one exact tag presentation and one payload presentation for each
declared coordinate. A
zero-payload variant therefore contributes only its tag; the Prover has no
completion presentation. Completion tags carry their exact external tag and
do not create a codec use. `coordinate_ordinal` is the zero-based position in
that variant's canonical K3-B coordinate-to-slot sequence; it is not a
Terminal output ordinal or an FS-failure tag.

A Decode obligation imports K3-B's exact decoder result
`Malformed | Decoded(T)` and transport law `Inactive | Active(T)`. It never
treats omitted or malformed input as an active semantic value. The obligation
index itself sorts by canonical body bytes; runtime frame and presentation
causality remains the imported K2/K3-B order and is not inferred from this
static sort.

The index contains exactly these generated rows, sorted by full
`EndpointStaticObligationBody` bytes with duplicates rejected. A row references
the identity-bearing graph law rather than copying actor, ports, state, or
presence fields. Thus exact graph equality plus the shared derivation law
entails exact static-obligation equality without creating a second semantic
copy.

### 7.2 Exact static requirements

Requirement discovery uses one exact graph-only least fixed point. Its
transient access rows are canonical derivation state, not a fourth contract
field or OIR identity input:

```text
EndpointValueAccessRouteBody =
    V(0,R{0:N(invocation_target_ref),1:N(slot_ref)})
  | V(1,N(constant_ref))
  | V(2,N(pure_node_ref))
  | V(3,N(decision_spine_ref))
  | V(4,N(verifier_message_spine_ref))
  | V(5,N(check_spine_ref))
  | V(6,R{0:N(challenge_spine_ref),1:N(challenge_law_ref)})
  | V(7,N(transport_edge_ref))
  | V(8,N(verifier_message_spine_ref))
  | V(9,N(check_spine_ref))
// InvocationDecode | Constant | PureEval | PlanMove
// LocalVerifierMessage | LocalCheck | ChallengeInterpret
// InboundTransport | ReconstructVerifierMessage | ReconstructCheck

EndpointValueAccessBody = R{
  0:EndpointValueRefBody(value),
  1:EndpointValueAccessRouteBody(route)
}
```

`EndpointValueAccessV0` seeds every endpoint value used by a selected K2
frame: every PublicBinding value, every guard input, every framed Prover- or
Verifier-message output, and every challenge-condition input. It also seeds
all Verifier-local action operands (deterministic message and Check inputs,
Reduction side inputs, and Terminal public outputs); the endpoint-value side
of every retained reachable Plan view read; and every endpoint-value-rooted
local presentation production or consumption. Runtime-only FS-failure
payloads, state versions, and decoder results are not endpoint-value seeds.
Earlier joint-Challenge-member refs and Terminal required-Check refs name
already admitted semantic rows rather than values; they add no independent
availability seed or requirement.

The worklist visits `EndpointValueRefBody` in full-body byte order and resolves
each demanded value exactly once. An invocation target uses its unique
selected ExternalSupply fibre/slot; a constant is intrinsic; a pure node adds
all ordered operands; a local Prover-message output uses its exact Plan move;
a local deterministic Verifier message or Check uses its exact algorithm and
adds its operands; and a Challenge uses its exact interpretation law. A
counterparty Prover-message output requires one inbound transport. A demanded
counterparty deterministic Verifier-message output uses an inbound transport
when one is selected, otherwise its public-reconstruction route recursively
adds its operands. A demanded counterparty Check output always uses its public-
reconstruction route because K3-B has no Check transport target. Zero routes,
multiple routes, an unavailable operand, or a nonlocal private leaf fails
formation.

The resulting access rows sort by full body bytes with duplicates rejected.
They determine requirement discovery but are not stored because every
nontrivial route is already exposed by one static obligation or requirement.
Every retained guard independently emits its evaluator use in both FS roles;
this does not depend on whether the guarded action is active at runtime.

The derived requirement sum contains local portable-evaluator uses,
counterparty contracts, one
`PrivateMaterialIngress(plan_private_ref, kind, type)` per selected private
material item, one
`PrivateRandomnessIngress(randomness_ref, type,
first_available_decision_spine_ref)` per selected randomness requirement, and
one `StateStorage(plan_state_ref, type, initializer, complete_update_row)` per
selected state cell. The first two are explicit ingress/authority obligations;
the last is an internal typed storage/lifetime obligation. None recovers an
excluded Plan key or chooses a realization.

The exact finite carrier is:

```text
CodecPathStepBody =
    V(0,N(field_ordinal)) | V(1,N(case_ordinal)) | V(2,U)
// RecordField | VariantCase | symbolic SequenceElement

AlgorithmUseSiteBody =
    V(0,N(pure_node_ref))
  | V(1,N(guard_spine_ref))
  | V(2,N(verifier_message_spine_ref))
  | V(3,N(check_spine_ref))
  | V(4,EndpointFrameRecipeBody)
  | V(5,N(challenge_law_ref))
  | V(6,N(challenge_law_ref))
  | V(7,N(challenge_law_ref))
  | V(8,N(challenge_law_ref))
  | V(9,N(plan_recipe_node_ref))
  | V(10,N(public_reconstruction_check_spine_ref))
  | V(11,R{0:EndpointPresentationCoordinateBody,
           1:CodecDirectionBody,
           2:S[CodecPathStepBody...],
           3:N(general_codec_ref)})
// PureNode | Guard | DeterministicVerifierMessage | Check | FsAbsorb
// FsSqueeze | FsAdvance | ChallengeAccept | ChallengeDecode | PlanRecipe
// PublicReconstruction | CodecPresentation

CounterpartyUseSiteBody =
    V(0,N(transport_edge_ref)) | V(1,N(counterparty_action_spine_ref))

OirRequirementBody =
    V(0,R{0:AlgorithmUseSiteBody,
          1:N(algorithm_dependency),2:N(evaluation_dependency)})
  | V(1,CounterpartyUseSiteBody)
  | V(2,R{0:N(private_material_ref),
          1:PrivateMaterialKindBody(kind),2:N(type_ref)})
  | V(3,R{0:N(randomness_ref),1:N(type_ref),
          2:N(first_available_decision_spine_ref)})
  | V(4,R{0:N(state_ref),1:N(type_ref),
          2:PlanInitializerBody(initializer),
          3:S[PlanUpdateBody(update)... in decision-spine order]})
// LocalEvaluator | Counterparty | PrivateMaterialIngress
// PrivateRandomnessIngress | StateStorage

EndpointCompletionInterfaceBody =
    V(0,S[N(completion_variant_ref)... in ref order]) | V(1,U)
// VerifierCompletions | NoSourceSemanticCompletion

DerivedEndpointContractBody(x) = R{
  0:S[EndpointStaticObligationBody... in full-body byte order],
  1:S[OirRequirementBody... in full-body byte order],
  2:EndpointCompletionInterfaceBody(x.completion_interface)
}

EndpointContractDerivationOutcomeBody =
    V(0,DerivedEndpointContractBody)
  | V(1,U) | V(2,U) | V(3,U) | V(4,U) | V(5,U) | V(6,U)
// Affirmative | MissingDependency | KindMismatch | Malformed | Refused
// DeterministicLimitExceeded | CheckerFailure
```

Derivation has no semantic Negative or Unsupported arm: after support and
graph formation it is one deterministic function. A contradiction in an
already formed graph is `CheckerFailure`; absent preimages and operational
limits retain their qualified branches. No nonaffirmative result carries a
partial contract.

The complete derived body independently satisfies K1's `2^20` encoded-byte,
`2^14` node, `2^14` aggregate-child-edge, and depth-384 limits. Derivation
also receives the request-local work limit used by extraction/admission.
General-codec path expansion is preflighted before any authoritative result is
returned. Oversize or work exhaustion is atomic qualified noncompletion with
no partial contract or cached prefix.

A local-evaluator requirement is emitted once per exact static use site. The
payload must equal the algorithm and evaluation dependencies already selected
by the graph action, pure node, Plan node, FS field, or resolved General-codec
law. Equal dependency IDs at different use sites do not merge.

Pure nodes are denotational definitions, not protected actions. A
`PureNode` use is generated only for a node reached by the exact
`EndpointValueAccessV0` least fixed point above, including public
reconstruction and the endpoint-value side of a reachable Plan view read. A
node retained solely to describe a counterparty Verifier message, Check,
Reduction, or Terminal produces no local evaluator requirement. If both local
and counterparty semantics reach the same node, exactly one local use is
emitted. A realization may memoize a total pure-node result after its operands
are available and before its first local demand; this does not authorize a new
observation or reorder the semantic spine.

Every statically retained potential local portable operation gets its exact
use-site row:
locally evaluated guards, deterministic Verifier messages and Checks; every
FS absorb recipe and the selected squeeze, advance, acceptance, and decode
laws; every reachable Plan recipe node; and every required General-codec leaf.
Fixed framing and namespace construction are selected semantic laws, not
portable dependency calls, so they do not invent evaluator requirements.

Codec uses are static schemas, not one identity row per runtime sequence
element. For each presentation, direction, and path from its root codec to a
General-codec leaf, the law emits one `CodecPresentation` use. A path is the
finite sequence of exact `RecordField`, `VariantCase`, and symbolic
`SequenceElement` steps. Runtime elements instantiate the symbolic step. The
General law's encoder or decoder is the dependency. Completion payload
coordinates use their individually selected slots; completion tags have no
codec path. A General law's admission-certificate verifier is not a runtime
endpoint use.

K2 permits a public Check output to feed later public computation. For a
Prover endpoint, the fixed law recursively derives
`PublicReconstruction(check_spine_ref)` for every and only Check in the
transitive predecessor closure of exhaustive Prover-local endpoint-value
roots: values needed by public-binding frames, local guards, challenge
conditions, locally demanded pure nodes, or the endpoint-value side of a
retained reachable Plan view read. The closure excludes `PlanValueRef` private material,
randomness, state, and recipe intermediates, which remain strategy-private and
are governed by Plan admission. A message value supplied through exact
counterparty transport is not reconstructed merely because it is public.

Every reconstructed Check must have K2 class `StaticPublic` or
`PublicHistory`, and its operands must be locally reconstructible in source
order. Reconstruction is a deterministic value use of the Check algorithm,
not a second semantic Check: it grants no Verifier authority, verdict, claim
transition, or terminal-check satisfaction. The Verifier retains the one
semantic Check occurrence.

The route for every locally demanded counterparty output is unique. A
Prover-message output requires one selected inbound transport. A deterministic
Verifier-message output uses one selected inbound transport when present;
otherwise, after `EndpointPublicClosureV0` succeeds, it emits exactly one
local `DeterministicVerifierMessage` evaluator use. A Check output uses the
`PublicReconstruction` route above. A Challenge is already a local public
derivation. Every other counterparty output requires one exact selected
transport or another profile-owned public-derivation rule. Zero routes or two
simultaneous routes fail formation.

Each selected cross-role transport edge and every counterparty-only semantic
action yields one counterparty requirement. Local reconstruction supplies a
value but never discharges actor authority, verdict, claim transition, or the
counterparty action itself. When that action's output is locally demanded, the
graph additionally requires exactly one value-availability route selected by
the preceding paragraph; otherwise source formation and local OIR admission
fail.

Requirements are sorted by full `OirRequirementBody` bytes with duplicates
rejected. At the Realization boundary the binding key is
`(OirId, OirRequirementBody)`; a requirement body alone grants no authority
and cannot be replayed against another endpoint. Runtime activity, draw
attempts, state versions, and dynamic sequence elements instantiate later
execution laws and do not multiply this static requirement set.

The completion interface is not a runtime outcome. The Verifier arm names
every Interface completion ref exactly once in ABI order; the
Plan-specialized Prover arm is `NoSourceSemanticCompletion` and requires an
empty completion table. Stage 4B owns which runtime completion, operational
noncompletion, interpretation failure, or verifier rejection occurs.

### 7.3 Claims, reductions, and role closure

Claims, reductions, and terminal closure remain identity-bearing graph
semantics, distinct from the derived static contract:

```text
SourceClaimAtom = {
  contract,
  Linear | Reusable,
  scope_event,
  Binding(binding_spine_event)
    | ReductionOutput(reduction_spine_event, output_ordinal)
}

SourceAnchoredObligation = {
    ReductionApplication {
      contract,
      scope_event,
      apply_spine_event,
      ordered input claims,
      ordered side inputs,
      ordered required challenge-law refs,
      ordered (publication_spine_event,
               optional next-challenge-law ref),
      ordered output slots with contract and all matching claim refs
    }
  | TerminalClaimClosure {
      terminal_spine_event,
      verdict,
      ordered public outputs,
      ordered required-true check spine events,
      ordered (claim ref, Consume | Discharge)
    }
}
```

The claim table preserves ascending original `ClaimRef` order. Anchored
obligations preserve their matching Reduction/Terminal spine-event order; the
spine is the cross-kind tie breaker. Every reduction output row retains all
and only matching claim refs and may therefore contain zero, one, or several.
A required publication points to the existing message/publication spine event
and retains its optional next-challenge law. Terminal closure retains every
required Check and claim disposition. K2 liveness, Last-Challenge, saturation,
stopping, and linear-closure laws can therefore be rerun from the graph.

The role split is fixed:

- Prover messages are local semantic productions for the Prover and
  counterparty requirements for the Verifier.
- Deterministic Verifier messages are local computations for the Verifier and
  counterparty requirements for the Prover.
- FS challenges are local public derivations in both roles, never ambient
  challenge inputs. Application-facing public-derivation exports are
  Verifier-owned.
- Checks, reductions, terminals, and the Protocol verdict are Verifier-owned;
  the Prover retains their exact counterparty obligations and any separately
  required public reconstruction.
- K2 supplies no semantic Prover completion. `Stop`, unavailable authority,
  private search exhaustion, and other operational noncompletion remain Stage
  4B subjects.
- FS sampling exhaustion is interpretation failure, not verifier rejection.

K3-D permits an explicitly trivial Core with no required Check. It preserves
every source-required Check but adds no universal nonempty-check policy.

## 8. Slot-centric role ABI

The Interface quotient preserves a graph, not flattened ABI atoms:

```text
RoleEndpointAbiGraph = {
  codec_nodes,
  slots,
  invocation_targets,
  invocation_fibres,
  statement_aliases,
  transport_edges,
  completion_variants
}
```

`codec_nodes` is the least transitive closure of codecs used by selected
slots. Structural child refs are densely rebased dependency-first; general
codecs retain the exact law declaration. `slots` retains every selected
external key exactly once in Interface-relative order and points to a local
codec.

Each nonempty invocation fibre contains one slot plus all role-selected K2
invocation targets mapped to it. This preserves K3-B's permitted many-to-one
inverse fibre and its equality assertion. A fibre never mixes public and
verifier-private targets. The Verifier selects both classes; the Prover selects
public inputs only.

A Statement alias contains a slot, binding spine event, and rebased
`SuppliesInvocation(target)` or `ExposesOpenedBinding`. It therefore preserves
the exact K3-B flow, same-slot invocation/Statement aliases, and one decoding
or Statement-exposure origin.

A transport edge preserves its exact spine target, source actor, destination,
and slot. Activity is the fixed spine law and the value type remains K3-B's
`Inactive | Active(T)`. Selection is exhaustive:

| Interface edge relative to endpoint role `R` | Selection and derived use |
|---|---|
| source `R`, destination `R` | selected local self-presentation |
| source `R`, destination other role | selected local counterparty output |
| source other role, destination `R` | selected counterparty input |
| source `R`, destination `ExternalApplication` | selected local export |
| `PublicDerivation`, destination `R` | selected local derived presentation, never an input |
| `PublicDerivation`, destination `ExternalApplication` | selected only by the Verifier as the unique application export owner |
| every other edge | complement, with no selected slot use from that edge |

Thus an FS challenge is locally derived in both endpoints. The
Interface-derived number of application exports is `0..n`; no transport entry
is silently synthesized.

A completion variant preserves the exact `CoreTerminal` or
`FiatShamirFailure` target, external tag, and complete coordinate-to-slot map,
including zero-payload terminals. The Verifier retains all applicable
completion entries. The Prover retains none.

Interface adequacy requires complete role-required invocation, Statement,
transport, public-derivation, completion, slot, and transitive codec coverage;
exact origin/alias laws; and no dead selected slot or codec. Admission of the
whole Interface alone is insufficient. A missing required counterparty
transport in an otherwise formed owner carrier is a source-profile `Refused`
result. A wrong edge shape or another malformed presentation is Interface
nonadmission. Neither becomes semantic `Negative`; OIR cannot repair either
ambiently.

## 9. Reachable Plan graph

After affirmative `PlanRealizes`, the Plan-specialized Prover quotient is:

```text
ReachablePlanGraph = {
  private_material,
  randomness,
  state,
  recipe_nodes,
  moves,
  updates
}
```

Reachability starts at every K2 prover-decision move payload and every
`ReplaceState` payload, then closes over recipe operands, selected-state
initializers, and recipe nodes. A `KeepState` entry alone does not select a
state slot. Once a state slot is selected, however, the quotient retains its
total update row at every decision, including `KeepState`. Each class has its
own dense ref universe. The view retains private-material kind/type but not its
external key; randomness type and first-availability boundary; state type and
initializer; recipe algorithm/evaluation/ordered operands/result and owning
decision; move; and state update.

K3-B observation coordinates remain semantic. A Plan view read therefore
retains both a rebased coordinate class and the value reached through that
coordinate. `OpenPublicInput(p)` and `OpenedBinding(b)`, or
`ObservedMessage(o)` and `PriorOwnMove(d)`, do not merge merely because their
runtime values can be equal. Every recipe-node output reference is owned by
one decision spine event, points backward inside that decision's node group,
and cannot be captured by a node, move, or update of another decision. In the
bounded base profile every decision is exactly one Prover-message spine event;
the Plan graph keys directly by that event rather than storing a duplicate
decision-obligation table.

Filtering follows source canonical order and then rewrites every edge through
the private source-to-view map. Dead declarations/nodes and
`derived_witness_exports` are absent. Plans differing only in those excluded
facts can share a quotient and OIR while retaining different exact-source
validation capabilities. Reachable recipe semantics is already above OIR;
concrete suppliers belong to Realization. The selected base Plan has no
below-OIR field branch.

## 10. Completion interface and role-closure laws

The exact `EndpointCompletionInterfaceBody` in Section 7 is the complete
static completion interface: the Verifier arm enumerates every Interface
completion ref exactly once in ABI order, while the Plan-specialized Prover
arm is `NoSourceSemanticCompletion` and has no completion ref. It is not a
claim about which runtime outcome occurs.

Source formation and local OIR admission each enforce four named graph laws:
no ambient FS challenge input, no Prover read of verifier-private inputs, no
Prover external completion, and no Plan read outside the classified reachable
Plan graph. They are not stored as a second absence table. Every predicate is
decidable from the complete semantic graph, so exact graph equality transfers
it automatically; a duplicate source-side echo would create no additional
coverage. A hidden host read is instead a later Realization nonconformance.

## 11. Identity, extraction, and authority

```text
EndpointSourceViewId(view) =
  ProfiledSemanticId<"pir.endpoint-source-view">(
    B, PirEndpointSourceViewProfileId,
    EndpointSourceViewDomainBody(view))
```

The K1 profiled wrapper contains `PirEndpointSourceViewProfileId` exactly once;
the domain body contains the purpose and every semantic universe above. The
carrier's `profile` field must equal that selected ID, but it is not copied into
the domain body. There is no extra hash argument for dependency closure,
purpose, source IDs, or maps. The read manifest ID is deliberately not in
quotient identity: two exact owner procedures deriving the same complete
meaning share the view ID.

Extraction requires the affirmative support capability, exact manifest and
schema-set authentication, Interface adequacy, optional exact
Plan/`PlanRealizes` join, owner read-set equality, canonical formation,
cumulative K1 limits, and request-local traversal limits. Only Affirmative
mints `CheckedEndpointSourceView`. No nonaffirmative result emits a partial
authoritative view.

The live capability retains the exact identical `SupportedExtractionBasis`
and its exact live `CheckedProjectionOwnerAdapterV0`, and binds exact source
handles, manifest, owner and dependency read receipts, private rebase maps,
and view ID. Every consumed bearer is process-registered, noncopyable, and
checked by recomputing its complete semantic ID/body relation. Cold recovery
reauthenticates and readmits the sources and dependency preimages,
reclassifies support, and reruns extraction. A body, ID, source map,
structurally equal reconstructed carrier, or sample execution never
reconstructs authority.

The bounded executable evidence also exposes an independent target constructor
that consumes this same exact `SupportedExtractionBasis` and its retained
adapter. It does not consume the resulting `CheckedEndpointSourceView`.
Consequently a joined witness can demonstrate one classification and one
authority chain feeding both independently implemented graph constructors,
without transferring source-view bytes or identity into local OIR admission.

## 12. Downstream boundary and non-claims

OIR independently constructs and admits a target, then a third checker applies
the relation in [OIR Projection Contract](../oir/projection-contract.md).
Bounded v0 admits no semantic reordering, split, fusion, or optimization, so
that relation is exact equality of the independently formed canonical
`EndpointSemanticGraphBody` plus purpose/role compatibility. A later
transformation needs a distinct checked refinement profile rather than
weakening this equality.
Source extraction establishes neither local OIR validity nor projection
correctness, endpoint pairing, execution success, proof acceptance, relation
satisfaction, or a cryptographic property.

Fresh, generic Prover, Oracle, module, optimized/reordered, and full execution
profiles remain later work. So do final MLIR syntax, Realization, portable
projection certificates, and general protocol-family coverage.

## Appendix A. Exact selected source-view body

All identified bodies below are exact K1 `MetaValueV0`. Use `U`, `N`, `Q`,
`Y`, `S`, `R`, and `V`; `CR(x)=Y(ContentRefV0(x))`,
`PR(x)=Y(PriorRefV0(x))`, `VT(T)=CanonicalValueTypeBody(T)`,
`FT(f)=CanonicalSemanticFailureTypeBody(f)`, and `DV(T,v)=v.datum` after exact
owner admission. Sequences preserve stated order; sets sort by full `M(item)`
bytes and reject duplicates. Sequence position is the local ref unless stated
otherwise.

The following imported value schemas are exactly those of the selected basis
and regime, never copies with local reinterpretation:

| Body | Owning appendix |
|---|---|
| `DeclarationRefBody`, `CanonicalValueTypeBody`, canonical datums and failure types | K1 [`executable-foundations.md`](../foundation/executable-foundations.md#appendix-a-exact-selected-v0-bodies) |
| `ModuleDeclarationRefBody`, `PublicBindingClassBody`, `CoinCorrelationBody`, `ReductionUsePolicyBody`, `TerminalVerdictBody`, `ClaimUsageBody`, `ClaimDispositionBody` | K2 [`interactive-core.md`](interactive-core.md#appendix-a-canonical-bodies) |
| construction algorithm and transition ABIs, `InfluenceAtomBody` | K2 [`fiat-shamir.md`](fiat-shamir.md#appendix-a-canonical-bodies) |
| transport actor/destination, completion-coordinate cases, and `PrivateMaterialKindBody` | K3-B [`interfaces-and-plans.md`](interfaces-and-plans.md#6-exact-canonical-bodies) |

Use under another `PriorMetaAuthenticationBasis`, `SemanticRegimeId`, or
incompatible exact-used language-profile closure is a kind/regime mismatch,
even when bytes happen to resemble the selected body.

```text
ChallengeModeBody = V(0,U) | V(1,U)
// Fresh | FiatShamir
EndpointPurposeBody =
    V(0,ChallengeModeBody) | V(1,ChallengeModeBody)
  | V(2,ChallengeModeBody)
// VerifierEndpoint | GenericProverEndpoint | PlanSpecializedProverEndpoint
// EndpointContractLawV0Body and EndpointSemanticGraphBody are imported
// exactly from OIR's Appendix A.  Their owning profile is named by the
// outer PirEndpointSourceViewProfileId wrapper.
EndpointRoleBody = V(0,U) | V(1,U)
// Verifier | Prover
OptionBody(None,F) = V(0,U)
OptionBody(Some(x),F) = V(1,F(x))

EndpointDependencyBody =
    V(0,CR(core_id)) | V(1,CR(construction_id))
  | V(2,CR(algorithm_id)) | V(3,CR(evaluation_contract_id))
  | V(4,CR(semantic_module_id))

EndpointValueRefBody =
    V(0,N(invocation_target_ref))
  | V(1,N(constant_ref))
  | V(2,N(pure_node_ref))
  | V(3,R{0:N(spine_event_ref),1:N(output_ordinal)})

SourceConstantBody(x) = R{0:N(type_ref),1:DV(type_table[type_ref],x.value)}
SourcePureNodeBody(x) = R{
  0:N(algorithm_dependency),1:N(evaluation_dependency),
  2:S[EndpointValueRefBody(input)...],3:N(result_type_ref)
}
```

The role ABI graph is exact and local:

```text
EndpointStructuralCodecBody =
    V(0,N(value_type_ref))
  | V(1,R{0:N(external_type_ref),1:N(semantic_type_ref),
          2:S[R{0:N(field_ordinal),1:N(local_codec_ref)}...]})
  | V(2,R{0:N(external_type_ref),1:N(semantic_type_ref),
          2:S[R{0:N(case_ordinal),1:N(local_codec_ref)}...]})
  | V(3,R{0:N(external_type_ref),1:N(semantic_type_ref),
          2:N(element_codec_ref)})
EndpointCodecNodeBody(x) = R{
  0:CR(x.interface_codec_id),
  1:V(0,EndpointStructuralCodecBody(x))
    | V(1,ModuleDeclarationRefBody(x.general_codec_law))
}
EndpointSlotBody(x) = R{0:Q(x.external_key),1:N(x.codec_ref)}
InvocationClassBody = V(0,U) | V(1,U)
// PublicInput | VerifierPrivateInput
InvocationTargetBody(x) = R{0:InvocationClassBody(x.class),1:N(x.type_ref)}
InvocationFibreBody(x) = R{
  0:N(x.slot_ref),1:S[N(invocation_target_ref)...]
}
StatementFlowBodyRebased = V(0,N(invocation_target_ref)) | V(1,U)
// SuppliesInvocation | ExposesOpenedBinding
StatementAliasBody(x) = R{
  0:Q(x.external_statement),1:N(x.slot_ref),2:N(x.binding_spine_ref),
  3:StatementFlowBodyRebased(x.flow)
}
TransportEdgeBody(x) = R{
  0:N(x.target_spine_ref),1:TransportActorBody(x.source),
  2:TransportDestinationBody(x.destination),3:N(x.slot_ref)
}
CompletionTargetBodyRebased = V(0,N(terminal_spine_ref)) | V(1,U)
CompletionCoordinateBodyRebased =
    V(0,R{0:N(terminal_spine_ref),1:N(output_ordinal)})
  | V(1,U) | V(2,U) | V(3,U) | V(4,U) | V(5,U) | V(6,U)
CompletionVariantBody(x) = R{
  0:CompletionTargetBodyRebased(x.target),1:Q(x.external_tag),
  2:S[R{0:CompletionCoordinateBodyRebased(coordinate),
        1:N(slot_ref)}... in coordinate-body order]
}
RoleEndpointAbiGraphBody(x) = R{
  0:S[EndpointCodecNodeBody...],1:S[EndpointSlotBody...],
  2:S[InvocationTargetBody...],3:S[InvocationFibreBody...],
  4:S[StatementAliasBody...],5:S[TransportEdgeBody...],
  6:S[CompletionVariantBody...]
}
```

Codec child refs point backward. Fibres are nonempty, cover each invocation
target exactly once, and are in target order. ABI table order is the filtered
Interface-relative order; no duplicated numeric `order` field exists.

The endpoint spine and value activity are:

```text
ActivityBody = V(0,U)
  | V(1,R{0:N(algorithm_dependency),1:N(evaluation_dependency),
          2:S[EndpointValueRefBody(input)...]})
// Always | Guarded
ScopeOpeningBodyRebased = V(0,U) | V(1,N(original_occurrence_ordinal))
EndpointMessageActionBody(x) = R{
  0:ModuleDeclarationRefBody(channel),1:N(result_type_ref)
}
EndpointVerifierMessageActionBody(x) = R{
  0:ModuleDeclarationRefBody(channel),
  1:N(algorithm_dependency),2:N(evaluation_dependency),
  3:S[EndpointValueRefBody(input)...],4:N(result_type_ref)
}
EndpointChallengeActionBody(x) = R{
  0:N(challenge_law_ref)
}
EndpointCheckActionBody(x) = R{
  0:N(algorithm_dependency),1:N(evaluation_dependency),
  2:S[EndpointValueRefBody(input)...],3:N(boolean_result_type_ref)
}
EndpointActionBody =
    V(0,EndpointMessageActionBody)
  | V(1,EndpointVerifierMessageActionBody)
  | V(2,EndpointChallengeActionBody)
  | V(3,EndpointCheckActionBody)
  | V(4,U)
  | V(5,U)
SourceSpineEventBody =
    V(0,U)
  | V(1,R{0:S[N(original_scope_ordinal)...],
          1:OptionBody(parent_scope_event_ref,N),
          2:ScopeOpeningBodyRebased(opening)})
  | V(2,R{0:N(original_binding_ordinal),1:N(scope_event_ref),
          2:PublicBindingClassBody(class),3:EndpointValueRefBody(value)})
  | V(3,R{0:N(original_occurrence_ordinal),1:N(scope_event_ref),
          2:ActivityBody(activity),3:EndpointActionBody(action)})
```

Formation requires one initialization event, a rooted scope-event tree, one
binding event per selected binding, one occurrence event per retained
occurrence, exact owner-derived total order, and the fixed prior-terminal/
FS-failure suppression law. The derived inverse index of ABI transport edges
by target spine event must consume every selected edge exactly once; actions
do not repeat that independently owned Interface subset.

Action tags 4 and 5 are Reduction and Terminal. Their exact anchor retains the
single spine backlink; storing the inverse ref in the action would create a
redundant cycle. Formation requires exactly one matching anchor for each such
action and no anchor for another action.

Occurrence output formation is exact: Prover message, Verifier message,
Challenge, and Check each have only output ordinal 0, with respectively the
declared result type, challenge value type, and exact K1 Boolean result type.
Reduction and Terminal have no `EndpointValueRef` output. Every occurrence
output ref points backward from its consumer.

Static FS bodies retain exact K2 frame coordinates while the fixed derivation
law constructs frame and namespace recipes from the spine:

```text
ChallengeEndpointLawBody(x) = R{
  0:N(original_challenge_ordinal),1:N(value_type_ref),
  2:ModuleDeclarationRefBody(domain),
  3:ModuleDeclarationRefBody(fresh_law),
  4:CoinCorrelationBody(correlation),
  5:ReductionUsePolicyBody(reduction_use),
  6:S[EndpointValueRefBody(condition)...],
  7:N(draw_bytes),8:N(maximum_draws),
  9:N(accept_algorithm_dependency),
 10:N(accept_evaluation_dependency),
 11:N(decode_algorithm_dependency),
 12:N(decode_evaluation_dependency)
}

StaticFsEndpointSemanticsBody(x) = R{
  0:N(core_dependency),1:N(construction_dependency),
  2:N(state_type_ref),3:N(bytes_type_ref),4:N(natural_type_ref),
  5:DV(type_table[state_type_ref],initial_state),
  6:N(absorb_algorithm_dependency),7:N(absorb_evaluation_dependency),
  8:N(squeeze_algorithm_dependency),9:N(squeeze_evaluation_dependency),
 10:N(advance_algorithm_dependency),11:N(advance_evaluation_dependency),
 12:ModuleDeclarationRefBody(application_domain),
 13:FT(sampling_exhausted_failure),
 14:DerivedPrefixLawBody,15:ChallengeTransitionLawBody,
  16:S[ChallengeEndpointLawBody(rule)...]
}
```

`DerivedPrefixLawBody = V(0,U)` and
`ChallengeTransitionLawBody = V(0,U)` select the exact K2 laws rather than an
authored callback. The derived namespace recipe is evaluated with a runtime
draw ordinal and contains no stored namespace datum.

Claim and anchor bodies are:

```text
ClaimSourceBodyRebased = V(0,N(binding_spine_ref))
  | V(1,R{0:N(reduction_spine_ref),1:N(output_ordinal)})
SourceClaimAtomBody(x) = R{
  0:ModuleDeclarationRefBody(contract),1:ClaimUsageBody(usage),
  2:N(scope_event_ref),3:ClaimSourceBodyRebased(source)
}
ReductionPublicationBodyRebased(x) = R{
  0:N(publication_spine_ref),
  1:OptionBody(next_challenge_law_ref,N)
}
ReductionOutputClaimBody(x) = R{
  0:N(output_ordinal),1:ModuleDeclarationRefBody(contract),
  2:S[N(output_claim_ref)... in ClaimRef order]
}
TerminalClaimDispositionBodyRebased(x) = R{
  0:N(claim_ref),1:ClaimDispositionBody(disposition)
}
SourceAnchoredObligationBody =
    V(0,R{
      0:ModuleDeclarationRefBody(contract),1:N(scope_event_ref),
      2:N(apply_spine_ref),3:S[N(input_claim_ref)...],
      4:S[EndpointValueRefBody(side_input)...],
      5:S[N(required_challenge_law_ref)...],
      6:S[ReductionPublicationBodyRebased(requirement)...],
      7:S[ReductionOutputClaimBody(output)...]
    })
  | V(1,R{
      0:N(terminal_spine_ref),1:TerminalVerdictBody(verdict),
      2:S[EndpointValueRefBody(public_output)...],
      3:S[N(required_check_spine_ref)...],
      4:S[TerminalClaimDispositionBodyRebased(disposition)...]
    })
```

For every reduction, field 7 has exactly one row per declared output contract
in output-ordinal order. The row's claim sequence equals every and only local
claim atom whose source is that reduction and output ordinal, in `ClaimRef`
order; it may be empty or contain several refs because K2 does not assert a
one-claim-per-output law. The one FS interpretation-failure type is obtained
from the enclosing static construction. No per-challenge or protected-action
copy is admitted.

Plan refs are class-specific:

```text
PlanValueRefBody =
    V(0,N(private_material_ref)) | V(1,N(randomness_ref))
  | V(2,N(state_ref)) | V(3,N(recipe_node_ref))
  | V(4,PlanViewReadBody(read))
  | V(5,R{0:N(type_ref),1:DV(type_table[type_ref],value)})
PlanViewCoordinateBodyRebased =
    V(0,N(constant_ref))
  | V(1,N(invocation_target_ref))
  | V(2,N(binding_spine_ref))
  | V(3,N(message_spine_ref))
  | V(4,N(challenge_spine_ref))
  | V(5,N(prior_decision_spine_ref))
PlanViewReadBody(x) = R{
  0:PlanViewCoordinateBodyRebased(x.coordinate),
  1:EndpointValueRefBody(x.value)
}
PlanInitializerBody = V(0,N(private_material_ref))
  | V(1,R{0:N(type_ref),1:DV(type_table[type_ref],value)})
PlanPrivateMaterialBody = R{0:PrivateMaterialKindBody(kind),1:N(type_ref)}
PlanRandomnessBody = R{0:N(type_ref),1:N(first_available_decision_spine_ref)}
PlanStateBody = R{0:N(type_ref),1:PlanInitializerBody(initializer)}
PlanRecipeNodeBody = R{
  0:N(owner_decision_spine_ref),
  1:N(algorithm_dependency),2:N(evaluation_dependency),
  3:S[PlanValueRefBody(input)...],4:N(result_type_ref)
}
PlanMoveBody = V(0,PlanValueRefBody)
// MessageValue; OracleValue and ModuleMove cannot reach the bounded graph
PlanMoveEntryBody = R{0:N(decision_spine_ref),1:PlanMoveBody(move)}
PlanUpdateBody = R{
  0:N(decision_spine_ref),1:N(state_ref),
  2:OptionBody(value,PlanValueRefBody)
}
PlanGraphBody(x) = R{
  0:S[PlanPrivateMaterialBody...],1:S[PlanRandomnessBody...],
  2:S[PlanStateBody...],3:S[PlanRecipeNodeBody...],
  4:S[PlanMoveEntryBody...],5:S[PlanUpdateBody...]
}
```

The closed `EndpointValueRefBody` has no Plan arm, which prevents recursive
self-wrapping and keeps K2-owned positions Plan-free. Every decision spine ref
must name a Prover-message action. Recipe nodes are grouped first by that ref
and then by their K3-B within-recipe order after reachable filtering.
Private-material, randomness, and state tables preserve filtered K3-B source
order. Move entries are strictly ascending by decision spine ref. Update
entries are strictly lexicographic by `(decision_spine_ref, state_ref)`.
Recipe-node order is strictly lexicographic by
`(owner_decision_spine_ref, within_recipe_ordinal)`. Every table rejects
duplicate keys.
A recipe-node operand points backward to a node with the same owner decision;
a move or update may reference only a node owned by its own decision. There is
exactly one move per decision spine and, for each selected state, exactly one
update per decision spine; `None` is K3-B `KeepState` and `Some` is
`ReplaceState`. Every
Plan edge is in range and the combined graph is acyclic under the admitted
decision schedule. A `PlanViewReadBody` must be the exact rebased K3-B
coordinate/value pair in that decision's admitted `StrategyDecisionView`.

The one PIR-owned source-view domain body is exactly:

```text
EndpointSourceViewDomainBody(x) = R{
  0:EndpointPurposeBody(x.purpose),
  1:EndpointSemanticGraphBody(x.semantic_graph)
}
```

`PirEndpointSourceViewProfileId` imports the exact
`OirEndpointGraphProfileId`, whose authenticated profile preimage owns the graph
schema and `EndpointContractLawV0`; `DeriveEndpointContractV0` is OIR's
evaluator. The law is not an authored graph field. The source view and OIR
endpoint therefore reach that same exact law through their authenticated
profile-import edge rather than by embedding a second profile-shaped body.

The complete K1 profiled body, not merely each domain table, must fit K1's
`2^20` encoded-byte, `2^14` node, `2^14` aggregate-child-edge, and depth-384
limits. Each local table is also bounded by `2^14`. Extraction has an
additional request-local visit/edge limit at most `2^17`; exhaustion is atomic
`DeterministicLimitExceeded`.

## Appendix B. Exact owner schema and read-manifest bodies

The selected design does not serialize a second copy of the K1/K2/K3-B grammar
or a producer-editable rule DAG. It commits to two fixed evaluator laws. The
first traverses the exact admitted owner bodies under the pinned regime; the
second assigns the purpose-specific disposition. This keeps the mechanism
small without making schema drift silent.

```text
OwnerSubjectBody = V(0,U) | V(1,U) | V(2,U) | V(3,U) | V(4,U)
// Protocol | Core | Construction | Interface | Plan
OwnerPathStepBody =
    V(0,N(field_ordinal))
  | V(1,N(variant_case))
  | V(2,N(sequence_index))
// Field | Case | Element
AtomicBoundaryBody =
    V(0,U) | V(1,U) | V(2,U) | V(3,U) | V(4,U)
  | V(5,U) | V(6,U) | V(7,U) | V(8,U) | V(9,U)
// Unit | Natural | Symbol | Bytes | PriorRef | ContentRef | DeclarationRef
// CanonicalValueType | SemanticFailureType | TypedCanonicalDatum
OwnerCoordinateBody(x) = R{
  0:OwnerSubjectBody(x.subject),
  1:S[OwnerPathStepBody(step)...],
  2:AtomicBoundaryBody(x.boundary)
}
RootGrammarLawV0Body = V(0,U)
K3DReadLawV0Body = V(0,U)
EndpointOwnerSchemaSetDomainBody = R{
  0:RootGrammarLawV0Body
}
EndpointReadManifestDomainBody(purpose) = R{
  0:EndpointPurposeBody(purpose),
  1:CR(EndpointOwnerSchemaSetId),
  2:K3DReadLawV0Body
}
```

The selected `SemanticRegimeId` is already fixed by `B`, and the exact source-
view profile ID is already field 0 of K1 `ProfiledSemanticBody`. Neither value
is repeated inside these domain bodies. The source-view profile's authenticated
import closure and law source bind the selected owner grammar and read law.

`RootGrammarLawV0` has exactly five roots in tag order: admitted Protocol,
its exact admitted Core, the Protocol's exact admitted Construction, its exact
admitted Interface, and optional exact admitted Plan. A Verifier request
requires the Plan root absent; a Plan-specialized Prover request requires it
present and an affirmative exact `PlanRealizes`. Protocol Fresh is traversable
only far enough to return the ordered unsupported result. Any unknown root,
field, variant, trailing field, sequence element grammar, atomic boundary, or
same-shaped body from another regime is a kind/regime failure, not an inert
coordinate.

The fixed evaluator recursively follows every field of the exact Appendix-A
owner bodies, including every option arm and every actual sequence element.
Traversal is depth-first in root-tag, record-field, variant-tag, and
sequence-index order. It emits one `OwnerCoordinateBody` for every typed atomic
boundary; the receipt retains the complete exact admitted subbody at that
boundary. There is no default or unknown arm. A source grammar change rotates
the semantic regime and therefore `EndpointOwnerSchemaSetId`; a policy or
derivation-law change rotates the K3-D profile/read-law tag. Implementations
must carry independent reflection or conformance vectors proving that the
visited coordinates equal the complete five-root grammar before this law may
mint source authority.

The fixed read law returns one disposition and one realized receipt for every
coordinate:

```text
ViewSinkBody =
    V(0,U) | V(1,U) | V(2,U) | V(3,U) | V(4,U)
  | V(5,U) | V(6,U) | V(7,U) | V(8,U) | V(9,U)
// Dependency | Type | Constant | PureNode | Abi | Spine | StaticFs
// Claim | Anchor | Plan
JoinAxisBody = V(0,U) | V(1,U) | V(2,U) | V(3,U)
// ProtocolCore | ConstructionCore | InterfaceProtocol | PlanProtocol
InertReasonBody =
    V(0,U) | V(1,U) | V(2,U) | V(3,U) | V(4,U)
  | V(5,U)
// SourceProvenanceOnly | VerifierPrivateForProver | DeadInterfaceElement
// PrivateMaterialKey | DeadPlanElement | DerivedWitnessExport
UnsupportedReasonBody =
    V(0,U) | V(1,U) | V(2,U) | V(3,U)
// FreshEndpoint | GenericProverEndpoint | StandardOracleEndpoint
// ModuleEffectEndpoint
DispositionBody =
    V(0,S[ViewSinkBody... in body-byte order]) | V(1,JoinAxisBody)
  | V(2,InertReasonBody) | V(3,UnsupportedReasonBody)
OwnerReadReceiptBody(x) = R{
  0:OwnerCoordinateBody(x.coordinate),
  1:x.exact_owner_subbody,
  2:DispositionBody(x.disposition)
}
```

The relevant arm contains a nonempty sorted-unique sink sequence. For a
relevant coordinate, the graph constructor reports the exact set of sinks to
which it actually contributed; it must equal this sequence, including when one
owner field contributes to several sinks. Join-only coordinates bind the live
source tuple and contribute no direct graph field; any separately retained K2
semantic content ID remains an ordinary graph operand. Inert coordinates also
contribute no direct graph field. A field inside an authenticated Core or
Construction preimage may nevertheless be transitively committed by the
retained K2 ID, and the dependency-read ledger records that hash-binding read.
Omitted Interface and Plan owner IDs confer no such indirect commitment. One
unsupported coordinate makes support
classification return no basis or partial authoritative receipt set. A
diagnostic may report every unsupported coordinate, ordered by the canonical
traversal above; an implementation cannot choose a more convenient first
error.

The selected root policy is exactly:

| Owner path | Verifier FS | Plan-specialized Prover FS |
|---|---|---|
| Protocol `.0 core_id` | Relevant Dependency/StaticFs | same |
| Protocol `.1 Fresh` | Unsupported Fresh | same |
| Protocol `.1 FS construction_id` | Relevant Dependency/StaticFs | same |
| Core `.0 semantic_modules` | role closure -> Dependency | same |
| Core `.1 public_inputs` | Relevant ABI/Type | same |
| Core `.2 verifier_private_inputs` | Relevant ABI/Type | Inert verifier-private |
| Core `.3 constants` | role closure -> Constant/Type | same |
| Core `.4 derived_values` | role closure -> PureNode/Dependency/Type | same |
| Core `.5 scopes` | role closure -> Spine | same |
| Core `.6 bindings` | Relevant Spine/StaticFs | same |
| Core `.7 challenges` | Relevant Spine/StaticFs | same |
| Core `.8 oracles` | Unsupported Oracle | same |
| Core `.9 checks` | role closure -> Spine/Dependency/Type/PureNode | same |
| Core `.10 claims` | Relevant Claim/Anchor | same |
| Core `.11 reductions` | Relevant Spine/Anchor | same |
| Core `.12 terminals` | Relevant Spine/Anchor | same |
| Core `.13 occurrences` base cases `0..5` | role closure -> Spine plus dependency/value closure | same |
| Core `.13` Oracle/module cases `6..7` | Unsupported exact case | same |
| Construction fields `0..10` | Relevant StaticFs/Dependency/Type | same |
| Interface `.0 protocol_id` | Join-only Interface | same |
| Interface `.1..6` | exact Interface endpoint closure -> ABI; complement inert | same, with all completion entries in complement |
| Plan root absent | required by request formation | illegal for this purpose |
| Plan `.0 protocol_id` | n/a | Join-only Plan |
| Plan selected private-material key | n/a | Inert private key |
| Plan selected private kind/type | n/a | Relevant Plan/Type |
| Plan complement private entry | n/a | Inert dead Plan material |
| Plan `.2 randomness`, `.3 state` | n/a | reachable closure -> Plan/Type |
| Plan `.4 recipes[*].1.nodes[*]` | n/a | selected node Relevant Plan; complement dead |
| Plan selected moves/updates | n/a | Relevant Plan |
| Plan `.5 derived_witness_exports` | n/a | Inert derived export |

The rows cover every current root field. Nested fields inherit the row's fixed
closure selector or its exact selected/complement result; there is no
most-specific-wins precedence. Current admitted Interface Oracle/module
targets are necessarily backed by the already-unsupported Core Oracle/module
case. A future Plan module constructor is a different owner grammar and fails
the pinned regime/schema join rather than inhabiting an unreachable current
`Unsupported` tag.

For every supported K2 owner row governed by `K2RoleSemanticClosure`, each
coordinate in the selector complement that is neither Prover-private nor an
unsupported Oracle/module case is exactly
`InertForPurpose(SourceProvenanceOnly)`. It contributes no direct graph field
but remains transitively committed through the retained Core or Construction
ID. This rule covers dead constants, pure nodes, semantic-module declarations,
and empty/unreached scope material and makes the five-root disposition total.

For a selected owner subtree, every atomic descendant selected by the closure
must be read at least once by the fixed Sections 4--10 graph constructor. A
read-tracking interpreter assigns that coordinate every and only sink tables
whose construction consumed it; zero sinks, an unselected read, or a sink not
named by the closed ten-sink grammar fails. Thus the multi-sink set is an
owner-law result, not a producer declaration. The independently traversed
root domain supplies the complement, so omitting both an output field and its
receipt cannot make extraction pass.

Selector algorithms are exact:

1. `AllElements` selects every element in source order.
2. `K2RoleSemanticClosure` starts independently of the output graph. It seeds
   every admitted base-effect occurrence (cases 0 through 5), its referenced
   scope and declaration, every public binding and challenge needed by the FS
   frame schedule, every claim/reduction/terminal closure fact, the role's
   invocation-input class, and every exact K2 coordinate named by an admitted
   Plan view read. It then follows `ValueRef` producers, guard and challenge
   inputs, scope parent/opening edges, occurrence operands/outputs, and
   claim/reduction/terminal edges to the least fixed point. Verifier seeds
   public and verifier-private local inputs; Prover seeds only public local
   inputs. Worklist order is increasing
   owner coordinate body; every edge is visited once. For the Prover it also
   requires `ProverEndpointValueClosure` before any ref is rebased.
3. `K3BInterfaceEndpointClosure` seeds public plus Verifier-private local
   invocation entries for the Verifier and public local invocation entries for
   the Prover; every Statement entry whose exact binding occurs in the spine;
   every transport entry whose exact target occurs in the spine and whose
   source/destination matches the exhaustive Section 8 role table; and all
   completion entries only for the Verifier. It then closes each selected use
   to its slot and each slot through the complete acyclic structural-codec
   child graph. It derives the exact selected/complement partition before
   rebasing.
4. `K3BPlanReachableClosure` seeds each admitted decision move payload and
   each `ReplaceState` payload. It follows recipe operands, selected-state
   initializers, and node dependencies to private, randomness, state, and
   nested recipe-node declarations. `KeepState` alone is not a seed; after a
   state is selected, its complete per-decision update row, including every
   `KeepState`, is retained. Node traversal is decision-local and follows
   exact K3-B view coordinates as well as their resolved values. Derived
   exports are never seeds.

Each selector is bounded by the source body's already admitted K1 limits plus
the extraction visit limit. Duplicate visits do not duplicate receipts.
Selected receipts are sorted by exact owner coordinate body before comparison
with the view constructor's read set. Complement is the exact finite owner
domain minus selected. Any nonpartition, dangling edge, role disagreement, or
limit exhaustion produces no view.
