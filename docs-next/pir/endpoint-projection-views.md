# Endpoint Projection Views

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative endpoint-projection target
> **Provisional owner:** `pir`
> **Authority:** This page defines the PIR-owned source side of the bounded
> endpoint-projection contract. It has no authority over the current
> specifications under [`docs/`](../../docs/README.md), does not activate full
> Stage 4B, and makes no implementation or cryptographic-security claim.

<!-- zkc-profile-source:endpoint-source-view-semantics:start -->

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
  | PlanContinuationProverEndpoint(ChallengeMode)
```

`EndpointProjectionSemanticsV0` supports exactly:

- `VerifierEndpoint(FiatShamir)` for the exact
  `PIRCanonicalFramedFSProfileId`; and
- `PlanSpecializedProverEndpoint(FiatShamir)` for that same family over the
  base PIR effects and current Plan grammar; and
- `PlanContinuationProverEndpoint(FiatShamir)` for that same family and
  grammar when owner-derived source reachability produces at least one
  nonempty accepted-terminal continuation arm.

The two Prover purposes are intentionally distinct. The specialized purpose
projects public proof-message decisions and the state needed to produce them.
The continuation purpose projects that same graph plus every derived export
promised by a nonempty accepted-terminal continuation arm. Such an arm may
contain decision-derived exports guaranteed on the path to that terminal,
same-terminal-derived exports, or both. An endpoint cannot claim the second
purpose by projecting those facts away, and the first purpose does not inherit
private continuation requirements merely because its source Plan declares
them. A continuation request whose exact Plan yields no nonempty arm returns
`Unsupported(NoPlanContinuationArm)` in the Plan-dependent support phase and
produces no partial view.

It returns early typed `Unsupported`, with no partial view, OIR, or proposition,
for Fresh endpoints, generic Plan-free Provers, any noncanonical transcript-
construction family, a Core with any native Oracle declaration or occurrence,
or an admitted module effect of any kind. A legacy module carrier without a supported PIR
effect contract stops earlier at PIR admission and never reaches this
classifier. A future Interface or Plan grammar containing module recipes has a
different exact owner profile/law closure and fails that join before this
classifier; the Foundation semantic regime need not change. The selected
endpoint-projection profile does not authenticate a foreign grammar merely to
return a feature label.

The support result is affirmative authority. A support-marked case cannot
later escape through `Unsupported`; disagreement by the selected evaluator is
`CheckerFailure`.

The semantic payloads are closed:

```text
EndpointUnsupportedReasonBody =
    V(0,U) | V(1,U) | V(2,U) | V(3,U) | V(4,U) | V(5,U)
// FreshEndpoint | GenericProverEndpoint
// StandardOracleEndpoint | ModuleEffectEndpoint
// OtherTranscriptConstructionFamily | NoPlanContinuationArm

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

The supported construction arm is closed by this consumer without importing
families it cannot project:

```text
DispatchEndpointTranscriptConstruction(exact authenticated admitted handle A) =
    CanonicalFramed
      iff AuthenticatedTranscriptConstructionProfile(A)
            = PIRCanonicalFramedFSProfileId
         and A is admitted by that exact profile
  | Unsupported(OtherTranscriptConstructionFamily)
      for any other exact authenticated admitted construction profile
  | qualified noncompletion
      for missing, wrong-kind/regime, malformed, refused, bounded, or
      checker-failing authentication
```

`PirEndpointSourceViewProfileId` imports the canonical-framed family because it
interprets that family's construction and transcript laws. The generic refusal
arm inspects only the already authenticated selected profile ID; it does not
open or interpret the foreign profile and therefore does not import duplex or
another unsupported family. There is no negative test that grants support: the
only affirmative arm is the exact positive canonical match. A future family
remains unsupported until a sibling endpoint profile explicitly imports and
interprets it.

Support classification has two ordered phases:

```text
EndpointFeatureSupportReasons(request) =
  CanonicalSortedUniqueSeq containing every applicable reason among
    FreshEndpoint
      iff request.challenge_mode = Fresh,
    GenericProverEndpoint
      iff request.purpose = GenericProverEndpoint(_),
    StandardOracleEndpoint
      iff request.core has any admitted Oracle declaration or occurrence,
    ModuleEffectEndpoint
      iff request.core has any admitted module-effect declaration or occurrence,
    OtherTranscriptConstructionFamily
      iff request.protocol.challenge_interpretation is FiatShamir(c) and
          DispatchEndpointTranscriptConstruction(request.construction_handle)
            returns Unsupported(OtherTranscriptConstructionFamily)

ClassifyEndpointProjectionSupport(request) =
  authenticate the request purpose and exact Protocol, Core, Construction when
    present, and Interface owner bases needed by EndpointFeatureSupportReasons;
  dispatch every FS construction through
    DispatchEndpointTranscriptConstruction;
  let feature_reasons = EndpointFeatureSupportReasons(request);
  if feature_reasons is nonempty, return Unsupported(feature_reasons);
  require DispatchEndpointTranscriptConstruction = CanonicalFramed;
  if request.purpose is VerifierEndpoint and a Plan root is supplied,
    return Malformed;
  for either Plan-specialized Prover purpose, if the exact Plan root or exact
    CheckedPlanRealizes preimage is absent, return MissingDependency;
  authenticate that Plan and CheckedPlanRealizes under their exact owner
    profile; if either is formed and structurally typed but fails its owner
    authentication/adequacy law or the result is nonaffirmative, return Refused;
  if request.purpose = PlanContinuationProverEndpoint(FiatShamir) and
     AcceptedPlanContinuationArmMap(protocol,plan) has no nonempty arm,
    return Unsupported([NoPlanContinuationArm]);
  otherwise derive and return one SupportedExtractionBasis
```

The first phase carries every and only applicable feature-level reason and
returns no extraction basis; a Core containing both Oracle and a module effect
therefore has two reasons, not an unspecified first error. The
Plan-continuation reason belongs only to the second phase. Consequently a
duplex continuation request with no arm returns only
`OtherTranscriptConstructionFamily`:
the classifier never authenticates or derives Plan continuation semantics for
an already unsupported construction family. This precedence is semantic and
cannot be changed by diagnostic traversal order.
Because no source-adequacy proposition is formed at this boundary, extraction
has no semantic `Negative`. A missing source is `MissingDependency`; a formed
owner carrier that fails the selected adequacy/profile law is `Refused`; and a
contradiction after affirmative owner admission is `CheckerFailure`. Wrong
edge shape remains Interface nonadmission. Recursive diagnostics are
non-authoritative. Only the
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
  | UnsupportedByEndpointProjection(reason)
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

`EndpointProjectionSemanticsV0` accepts only the selected v0 `SemanticRegimeId`
`0c537a1d1638992bd0c3efd2256ed4c3506ecb96bb6136b6084189de10b86bef`
and the following exact-used profile import DAG:

```text
PIRInteractionProfileId ---------+
PIRCanonicalFramedFSProfileId ---+
PIRInterfacePlanProfileId -------+--> PirEndpointSourceViewProfileId
OirEndpointGraphProfileId -------+                 |
                                  +-----------------+--> OirProjectionRelationProfileId
OirEndpointGraphProfileId -----------------------------^
```

The source-view profile directly imports all four profiles because its
projector opens Interaction, canonical-framed construction, and
Interface/Plan owner declarations while constructing the OIR-owned graph
grammar. The OIR graph profile is an import-free target-language root: opaque
typed content and declaration references in a graph do not authorize it to
open their foreign semantics. The projection relation directly imports the
two languages it compares. Every arrow is an exact-used `profile_imports`
edge, not an ambient bundle hash, textual version label, or transitive-use
shortcut. The older bounded executable baseline exercised only the
pre-composition graph with the following profile-ID digests under the selected
regime, in the same order:
`3249d35408bd507c6613eb2d7496b95c6d3313a85bac41f28751d1957d6e4f8c`,
`6138f0ffe95880b2cfe0a4ccd3da71610974193a2fcf6aaa60ae3cf7bfacdfa4`,
`ccb080314d48881cf89d8b59bc3d14364311797b49f2048b31fd59e684fbaaa7`,
`cf79a520db90374e7c1bbed17cda79c20130e479a538de9c8a41826b62a60330`,
and `b183c8af6fad580b0c4d003f4b4e3c26e08fca63dff0b6cf36f6b210091a89fd`.
The accepted-terminal Plan extension and the now-explicit two-family
composition both rotate that old chain, so these digests no longer
authenticate the selected Plan, endpoint, or OIR grammar and are retained only
as pre-rotation bounded evidence. This is a profile/law mismatch, not a
Foundation `SemanticRegimeId` rotation: the Foundation semantic regime above
remains unchanged. The identity equations below consume full typed profile
IDs, never bare digest strings. These values are not durable selected
constants. They do not supply the complete canonical
`SemanticLanguageProfileBody` preimages or establish durable owner-profile byte
parity. Until those complete owner profile preimages are published, this page
fixes the ideal target equations and import topology, not independently
reconstructible profile IDs.

The source-view profile supports exactly the following portable semantic
subject kinds, in ASCII order:

```text
pir.endpoint-owner-schema-set
pir.endpoint-owner-supplement
pir.endpoint-read-manifest
pir.endpoint-source-view
pir.source-binding-payload
pir.source-capability-requirement
pir.source-consumer
pir.source-no-policy
pir.source-policy-closure
pir.source-purpose
```

The first four are the owner-schema contract, bounded residual supplement,
purpose-specific manifest, and complete source quotient. The remaining six
are this profile's inert source-authority artifacts and nominal consumer and
purpose roles. `SupportedExtractionBasis`, provisional or activated bearers,
`CheckedProjectionOwnerAdapterV0`, checked dependency closure, checked source
view, capabilities, validation requests, operation results, receipts retained
only by a live capability, and diagnostics are process-local operation state;
none is a portable supported subject. Listing such a bearer-shaped object in
the profile is malformed rather than a serialization feature.

The owner-schema-set and read-manifest IDs are formed under the exact source-
view profile. A same-shaped future regime or profile does not inherit this
policy. A change to Interface/Plan meaning rotates the endpoint graph, source
view, and projection relation; a source-view change rotates source and
projection; and a projection-law change rotates the relation profile. The live
validation operation is owned by that relation profile and has no separate
semantic identity layer. A Relations-only K3-B profile change remains outside
this exact Interface/Plan-rooted profile closure and therefore does not rotate
the OIR chain. There is no wildcard, default,
authored callback, textual reason, or precedence rule. Missing, extra, or
unknown schema edges fail before extraction.

The four closed sequence selectors are owner algorithms:

```text
AllElements
ProtocolRoleSemanticClosure
InterfaceEndpointReachableClosure
PurposeSelectedPlanReachableClosure
```

`PurposeSelectedPlanReachableClosure` is purpose-parameterized. For the ordinary Plan-
specialized purpose it closes only public Prover decisions and their selected
state. For the continuation purpose it additionally seeds every export in
every owner-derived nonempty accepted-terminal arm, then closes through each
export's exact decision or terminal site, local recipe nodes, private ingress,
randomness, and state dependencies. The common algorithm name does not permit
a caller to choose its seeds.

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

The portable supplement and its inert source-authority artifacts are exact
semantic subjects. Live activation state is not:

```text
EndpointOwnerSupplementFamily = "endpoint-owner-supplement-v0"

FutureOwnerSupplementV0 = {
  protocol_id: ProtocolId,
  core_id: CoreId,
  construction_id: TranscriptConstructionId,
  interface_id: ProtocolInterfaceId,
  plan_id: None | Some(ProverPlanId),
  purpose: EndpointProjectionPurpose,
  owner_schema_set_id: EndpointOwnerSchemaSetId,
  read_manifest_id: EndpointReadManifestId,
  residual_receipts:
    NonEmptyCanonicalSortedUniqueSeq<OwnerReadReceipt>
}

FutureOwnerSupplementBodyV0(x) = R{
  0:CR(x.protocol_id),1:CR(x.core_id),2:CR(x.construction_id),
  3:CR(x.interface_id),4:EndpointOptionBody(x.plan_id,CR),
  5:EndpointPurposeBody(x.purpose),6:CR(x.owner_schema_set_id),
  7:CR(x.read_manifest_id),
  8:S[OwnerReadReceiptBody(receipt)... in owner-coordinate body order]
}

FutureOwnerSupplementId(x) =
  ProfiledSemanticId<"pir.endpoint-owner-supplement">(
    B, PirEndpointSourceViewProfileId,
    FutureOwnerSupplementBodyV0(x))

EndpointSupplementBindingPayloadBody(x) = R{
  0:Q(EndpointOwnerSupplementFamily),1:CR(x.supplement_id),
  2:CR(x.owner_schema_set_id),3:CR(x.read_manifest_id),
  4:CR(x.consumer_id),5:CR(x.purpose_id),
  6:Q("whole-endpoint-owner-supplement-v0")
}
EndpointSupplementCapabilityRequirementBody(x) = R{
  0:Q(EndpointOwnerSupplementFamily),1:CR(x.binding_payload_id),
  2:CR(x.no_policy_id),3:CR(x.consumer_id),4:CR(x.purpose_id),
  5:Q("fresh-identical-activated-supplement-bearer")
}
EndpointSupplementNoPolicyBody(x) = R{
  0:Q(EndpointOwnerSupplementFamily),1:CR(x.supplement_id)
}
EndpointSupplementPolicyClosureBody(x) = R{
  0:Q(EndpointOwnerSupplementFamily),1:CR(x.binding_payload_id),
  2:CR(x.no_policy_id),3:CR(x.capability_requirement_id)
}

EndpointSupplementBindingPayloadId(x) =
  ProfiledSemanticId<"pir.source-binding-payload">(
    B,PirEndpointSourceViewProfileId,
    EndpointSourceBindingPayloadBody(Supplement(x)))
EndpointSupplementCapabilityRequirementId(x) =
  ProfiledSemanticId<"pir.source-capability-requirement">(
    B,PirEndpointSourceViewProfileId,
    EndpointSourceCapabilityRequirementBody(Supplement(x)))
EndpointSupplementNoPolicyId(x) =
  ProfiledSemanticId<"pir.source-no-policy">(
    B,PirEndpointSourceViewProfileId,
    EndpointSourceNoPolicyBody(Supplement(x)))
EndpointSupplementPolicyClosureId(x) =
  ProfiledSemanticId<"pir.source-policy-closure">(
    B,PirEndpointSourceViewProfileId,
    EndpointSourcePolicyClosureBody(Supplement(x)))

EndpointSourceBindingPayloadBody(x) =
  V(0, EndpointSupplementBindingPayloadBody(y)) if x = Supplement(y)
EndpointSourceCapabilityRequirementBody(x) =
  V(0, EndpointSupplementCapabilityRequirementBody(y)) if x = Supplement(y)
EndpointSourceNoPolicyBody(x) =
  V(0, EndpointSupplementNoPolicyBody(y)) if x = Supplement(y)
EndpointSourcePolicyClosureBody(x) =
  V(0, EndpointSupplementPolicyClosureBody(y)) if x = Supplement(y)
```

The four `EndpointSource*Body` compilers are this profile's `pir.source-*`
subject bodies: one closed variant per kind over exactly the source families
the profile issues, which today is the supplement family alone, tagged
`Supplement(y)`. Each identity constructor above applies `ProfiledSemanticId`
to a compiler's output, so the subject's body is the tagged variant and no
family-local record is a preimage on its own. A payload of another profile's
family has no arm here.

The residual sequence is exactly the subset of Appendix B owner coordinates
assigned to the supplement path set, with no overlap, omission, or additional
coordinate. Its root IDs, purpose, schema set, and manifest must equal the
support request. A receipt carries the exact public semantic source subbody,
not a runtime secret, private assignment, capability, checker result, or
producer-selected graph. The binding payload, no-policy artifact, requirement,
and closure are inert identities. Activation validates them and mints one
fresh process-local bearer; no ID, body, digest, or reconstructed equal object
is that bearer.

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

Static obligations, requirements, the external completion interface, and the
optional private Plan-continuation contract are not four more authored tables.
The fixed `DeriveEndpointContractV0` law in Section 7 derives them uniquely
from this graph. This avoids two semantic copies of the same action while
retaining an exact static conformance and requirement boundary for OIR and
Realization.

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
EndpointSpineEvent =
    FsInitialization
  | ScopeOpening {
      core_scope_path,
      parent_scope_event,
      Initially | BeforeOccurrence(core_occurrence_ordinal)
    }
  | PublicBinding {
      core_binding_ordinal,
      scope_event,
      class,
      value
    }
  | CoreOccurrence {
      core_occurrence_ordinal,
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

Sequence position is the local `EndpointSpineEventRef`. Scope and binding events
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

This section is the canonical-framed sibling only. The source view retains the
exact construction state/bytes/natural types,
initial state, absorb/squeeze/advance algorithms and contracts, application
domain, sampling-failure type, challenge rules, K2 frame law, exact derived
prefix law, and exact retry/state-advance law. The per-draw namespace recipe is
derived from those fields plus the challenge action's exact spine scope and
original K2 coordinate; it is not stored a second time. Runtime values and
receipts do not enter identity. Challenge laws preserve ascending original K2
`ChallengeRef` order.

K2 framing distinguishes graph refs from semantic frame coordinates:

```text
ProtocolFrameCoordinate =
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
  completion_interface,
  private_plan_continuation
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

`completion_interface` describes only externally presented Protocol
completion. `private_plan_continuation` is a separate static contract for
internal Plan continuation values and never changes, extends, or satisfies
that external completion interface. Both supported Prover purposes therefore
keep `NoSourceSemanticCompletion`; the ordinary purpose has no continuation
contract, while the continuation purpose derives one from exact graph-local
accepted-terminal arms.

### 7.1 Closed static-obligation index

The static-obligation index is generated by one fixed law. It is neither an
authored action table nor an execution order. OIR physically owns
`EndpointFrameRecipeBody`, `EndpointPresentationCoordinateBody`,
`CodecDirectionBody`, and `EndpointStaticObligationBody` in
[its exact contract appendix](../oir/projection-contract.md#appendix-a-exact-oir-and-projection-bodies).
This PIR source-view specification imports those bodies without copying or
reinterpreting their tags. In particular, the imported tag 6 is exactly
`PlanContinuation(accepted_terminal_ref)`.

`SlotIngress` occurs once for every selected external-supply slot. Invocation
fibres and `SuppliesInvocation` Statement aliases share that one ingress; they
never create duplicate decoding authority.

`PlanDecision` occurs once for each retained Prover-message move entry in
either Prover graph. It imports the exact reachable Plan decision:
view reads, private material, randomness availability, state row, recipe DAG,
move, and total selected-state update row. The obligation does not prescribe
a concrete supplier, entropy source, storage device, or guarded runtime state
merge.

`PlanContinuation(terminal_ref)` occurs exactly once for each retained
nonempty accepted-terminal arm in a continuation-purpose graph and never for
the ordinary Plan-specialized purpose. It imports the exact `Accept` terminal,
the sealed final Plan-state source, every arm export and its source site, the
export-rooted site-local recipe closure, and the all-or-nothing arm law. For a
decision-derived export it also imports the owner-derived guarantee that the
source decision is active and ordered before that terminal on every path that
reaches it. For a terminal-derived export it requires the export site to be
that identical terminal. This is a static obligation; it neither reaches a
runtime terminal nor issues a private value.

`TranscriptFrame` occurs for Core, Construction, and application-domain initialization
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
transient `EndpointValueAccessBody` rows are canonical derivation state, not a
fourth contract field or OIR identity input. OIR physically owns that body and
`EndpointValueAccessRouteBody`; PIR imports both exact bodies from the same
contract appendix.

`EndpointValueAccessV0` seeds every endpoint value used by a selected K2
frame: every PublicBinding value, every guard input, every framed Prover- or
Verifier-message output, and every challenge-condition input. It also seeds
all Verifier-local action operands (deterministic message and Check inputs,
Reduction side inputs, and Terminal public outputs); the endpoint-value side
of every retained reachable Plan view read; and every endpoint-value-rooted
local presentation production or consumption. Runtime-only FS-failure
payloads, state versions, and decoder results are not endpoint-value seeds.
Earlier joint-Challenge-member refs and Terminal required-Check,
required-Reduction, and terminal-claim refs name already admitted semantic
rows rather than values; they add no independent availability seed or
requirement.

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

OIR physically owns the exact finite requirement carrier and aggregate
contract bodies: `CodecPathStepBody`, `AlgorithmUseSiteBody`,
`CounterpartyUseSiteBody`, `OirRequirementBody`,
`EndpointCompletionInterfaceBody`, `PrivatePlanContinuationAccessBody`,
`PlanContinuationOutputDeclBody`,
`AcceptedPlanContinuationArmDeclBody`,
`PrivatePlanContinuationContractBody`, `DerivedEndpointContractBody`, and
`EndpointContractDerivationOutcomeBody`. PIR imports and names those exact
bodies from the OIR contract appendix. It does not define a second body or
choose different field names. The private semantic carrier named by the
imported bodies is exactly
`PrivatePlanContinuationAccess =
PlanContinuationOutput(PlanContinuationOutputRef)`.

Contract derivation applies one exact-use law to the private namespace. For an
ordinary Plan-specialized purpose the option is `None` and no
`PrivatePlanContinuationAccessBody` may occur. For a continuation purpose the
option is `Some`, every access resolves to one in-range
`PlanGraphDerivedExportBody`, every retained graph export is selected by at
least one arm, every arm output occurs exactly once in that arm, and no access
appears outside this contract. Missing, extra, dangling, duplicate, wrong-site,
wrong-type, or generic-value substitution is formation failure, not a partial
contract.

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
laws; every reachable Plan recipe node at its exact decision or accepted-
terminal site; and every required General-codec leaf.
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
every Interface completion ref exactly once in ABI order; both Prover purposes
are `NoSourceSemanticCompletion` and require an empty external completion
table. The ordinary Plan-specialized purpose has
`private_plan_continuation = None`. The continuation purpose has
`private_plan_continuation = Some(contract)`, where the contract lists every
and only nonempty accepted-terminal arm in terminal order and each arm lists
its complete output set in graph-local ref order. Each ref resolves through
the dedicated `PrivatePlanContinuationAccessBody`, never through
`EndpointValueRefBody`; each source site and type must equal the selected
export. Every arm is atomic: no proper prefix or subset is a result, and an
inactive terminal has no value rather than an empty tuple. The contract carries
no runtime value, live capability, or evidence that a continuation was issued.
PIR Plan execution owns any later runtime issuance; OIR projection here remains
static. Runtime OIR and Realization own reached completion, continuation
success or operational noncompletion, interpretation failure, and verifier
rejection.

### 7.3 Claims, reductions, and role closure

Claims, reductions, and terminal closure remain identity-bearing graph
semantics, distinct from the derived static contract:

```text
EndpointClaimAtom = {
  contract,
  Linear | Reusable,
  scope_event,
  Binding(binding_spine_event)
    | ReductionOutput(reduction_spine_event, output_ordinal)
}

EndpointAnchoredObligation = {
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
      sorted-unique required-true check spine events,
      sorted-unique required-reduction spine events,
      sorted-unique terminal claim refs
    }
}
```

The claim table preserves ascending original `ClaimRef` order. Anchored
obligations preserve their matching Reduction/Terminal spine-event order; the
spine is the cross-kind tie breaker. Every reduction output row retains all
and only matching claim refs and may therefore contain zero, one, or several.
A required publication points to the existing message/publication spine event
and retains its optional next-challenge law. Terminal closure retains every
required Check, every required Reduction, and every terminal claim; the claim
disposition is derived from the verdict and is not a stored field. K2
liveness, Last-Challenge, saturation, stopping, and linear-closure laws can
therefore be rerun from the graph.

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

After affirmative `PlanRealizes`, either Prover quotient uses the same closed
graph carrier:

```text
ReachablePlanGraph = {
  private_material,
  randomness,
  state,
  site_qualified_recipe_nodes,
  decision_moves,
  decision_updates,
  site_qualified_derived_exports
}

PlanContinuationOutputRef =
  dense ordinal into site_qualified_derived_exports
```

Ordinary reachability starts at every InteractiveCore prover-decision move
payload and every `ReplaceState` payload, then closes over site-local recipe
operands, selected-state initializers, and decision recipe nodes. It retains no derived export
merely because the Plan declares one. Continuation reachability has all those
seeds and additionally seeds every export in at least one exact nonempty
accepted-terminal arm. It then closes through each export's decision or
accepted-terminal site, site-local nodes, public reads, private material,
randomness, and state dependencies. A `KeepState` entry alone does not select
a state slot. Once a state slot is selected, the quotient retains its total
update row at every decision, including `KeepState`.

The arm set is owner-derived before rebasing. For each exact admitted `Accept`
terminal `t`, its arm contains every and only:

1. decision-derived export whose exact source decision is guaranteed active
   and ordered before `t` by InteractiveCore's scope-opening,
   guard-implication, and causal-order laws; and
2. accepted-terminal-derived export whose source site is exactly `t`.

The fixed source law takes both the admitted Protocol and the exact admitted
Plan. `AcceptedPlanContinuationArm(P,plan,t)` is imported unchanged from the
Plan owner's checked lifecycle law; this endpoint document only derives its
complete map:

```text
GuaranteedDecisionBeforeAcceptedTerminal(P,plan,d,t) :=
  plan is the exact admitted Plan for P
  and CheckedPlanRealizes(P,plan) is affirmative
  and t is an exact Accept terminal of P
  and d is an exact Prover decision of P
  and Occurrence(d) strictly precedes TerminalOccurrence(t)
  and every scope needed by d is guaranteed open on the t-active path
  and GuardImplies(guard(t),guard(Occurrence(d)))

AcceptedPlanContinuationArmMap(P,plan) :=
  every and only (t,AcceptedPlanContinuationArm(P,plan,t))
  whose derived sequence is nonempty, in TerminalRef order
```

`GuardImplies`, scope opening, and
`GuaranteedDecisionBeforeAcceptedTerminal(P,plan,d,t)` are the exact owner
laws consumed by the Plan's checked lifecycle-read basis; neither a sample run
nor a producer-supplied Boolean can establish them. Every caller supplies the
same exact admitted `(P,plan)` from the affirmative extraction basis; no
ambient Plan lookup or protocol-only overload exists. Each source export is
considered once per exact terminal. Each arm rejects duplicates before
rebasing; the same source export may still appear once in every distinct arm
whose path guarantee holds.

An arm with no such export is absent. A decision export guaranteed before
several accepted terminals appears in each applicable arm through the same
graph-local output ref. A terminal export appears only in its own arm. A
conditionally active decision export that is not guaranteed on `t`'s path is
not promised by that arm. The continuation purpose is supported only when the
complete derived arm map contains at least one nonempty arm.

Each class has its own dense ref universe. The view retains private-material
kind/type but not its external key; randomness type and first-availability
boundary; state type and initializer; recipe algorithm/evaluation/ordered
operands/result and exact source site; move and state update; and every
selected export's exact source site, local value, and type. Witness-surface
keys are source provenance and are not graph fields. Every selected export is
assigned one `PlanContinuationOutputRef`; same-valued or same-typed exports
remain distinct.

K3-B observation coordinates remain semantic. A Plan view read therefore
retains both a rebased coordinate class and the value reached through that
coordinate. `OpenPublicInput(p)` and `OpenedBinding(b)`, or
`ObservedMessage(o)` and `PriorOwnMove(d)`, do not merge merely because their
runtime values can be equal. Every recipe-node output reference is owned by
one exact decision or accepted-terminal site, points backward inside that
site's node group, and cannot be captured by another site. Moves and state
updates may reference only decision-site values. An accepted-terminal node may
read only the coordinates affirmed by the Plan owner's exact terminal-read
law and the sealed final-state source; it has no move, randomness ingress, or
state-update arm. In the bounded base profile every decision is exactly one
Prover-message spine event, so decision sites key directly by that event.

Filtering follows source canonical order and then rewrites every edge through
the private source-to-view map. Dead declarations, nodes, and unselected
exports are absent. The ordinary purpose may therefore share one quotient with
a Plan that differs only in continuation-inert facts; the continuation purpose
may not erase any selected arm, export, or dependency. Reachable recipe
semantics is already above OIR; concrete suppliers and runtime continuation
issuance are not. The selected base Plan has no below-OIR field branch.

## 10. Completion interface and role-closure laws

The exact `EndpointCompletionInterfaceBody` in Section 7 is the complete
static completion interface: the Verifier arm enumerates every Interface
completion ref exactly once in ABI order, while both Prover purposes use
`NoSourceSemanticCompletion` and have no completion ref. The private
continuation contract is a separate terminal-indexed field and is not a
Protocol completion claim.

The direct Plan-owned next-ingress handoff is outside the endpoint value and
OIR runtime domains: it has no `EndpointValueRef`, no OIR runtime operation or
runtime value, and no serialized capability. The static continuation contract
only says which private outputs a later consumer may request after the exact
accepted terminal. PIR Plan execution separately owns reaching that terminal,
atomically producing the arm, and issuing any live access right; none of those
runtime facts is present in this source view or its projected OIR graph.

Source formation and local OIR admission each enforce four base graph laws plus
one exact accepted-terminal arm-closure law: no ambient FS challenge input, no
Prover read of verifier-private inputs, no Prover external completion, no Plan
read outside the classified reachable Plan graph, and exact accepted-terminal
arm closure. The arm-closure law checks every
and only nonempty `Accept` arm, decision-path guarantees, same-terminal
ownership, graph-local ref and type agreement, site-local node reachability,
and atomic all-or-nothing membership. `PrivatePlanContinuationAccessBody` is
legal only in that contract; its presence in an `EndpointValueRefBody`,
InteractiveCore value, ABI edge, public-closure root, Plan move, or state update
is malformed.
These laws are not stored as a second absence table. Every predicate is
decidable from the complete semantic graph, so exact graph equality transfers
it automatically; a duplicate source-side echo would create no additional
coverage. A hidden host read or an attempted runtime issuance without the
PIR-owned continuation operation is instead a later Realization
nonconformance.

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

Neither `SupportedExtractionBasis`, `CheckedEndpointSourceView`, nor a later
affirmative projection capability contains a completed Plan continuation or a
live PIR continuation right. They authorize only the static source quotient
and its comparison with a static OIR graph. Runtime access to an active arm
requires the independently issued PIR Plan continuation result and capability;
adding that dynamic input to an OIR executor remains a later Realization law.

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
and regime. The OIR rows are target constructors, not aliases of PIR bodies:
this profile owns the total source-to-target mapping and cannot reinterpret or
extend an OIR tag locally.

| Body | Owning appendix |
|---|---|
| `DeclarationRefBody`, `CanonicalValueTypeBody`, canonical datums and failure types | K1 [`executable-foundations.md`](../foundation/executable-foundations.md#appendix-a-exact-selected-v0-bodies) |
| `ModuleDeclarationRefBody`, `PublicBindingClassBody`, `CoinCorrelationBody`, `ReductionUsePolicyBody`, `TerminalVerdictBody`, `ClaimUsageBody`, `ClaimDispositionBody` | K2 [`interactive-core.md`](interactive-core.md#appendix-a-canonical-bodies) |
| construction algorithm and transition ABIs, `InfluenceAtomBody` | K2 [`fiat-shamir.md`](fiat-shamir.md#appendix-a-canonical-bodies) |
| source Interface and Plan bodies used by extraction | [`interfaces-and-plans.md`](interfaces-and-plans.md#6-exact-canonical-bodies) |
| every `Endpoint*Body`, `RoleEndpointAbiGraphBody`, `StaticFsEndpointSemanticsBody`, `Plan*Body`, aggregate graph, static-obligation, requirement, completion, continuation, and contract body | OIR [`projection-contract.md`](../oir/projection-contract.md#appendix-a-exact-oir-and-projection-bodies) |

Use under another `PriorMetaAuthenticationBasis`, `SemanticRegimeId`, or
incompatible exact-used language-profile closure is a kind/regime mismatch,
even when bytes happen to resemble the selected body.

The source-to-target body mapping is closed and injects no source identity:

```text
MapEndpointPurposeV0(PIR purpose) -> OIR EndpointPurposeBody
MapEndpointRoleV0(PIR role) -> OIR EndpointRoleBody
MapEndpointDependencyV0(authenticated PIR dependency) -> OIR EndpointDependencyBody
MapEndpointValueRefV0(selected and rebased PIR value ref)
  -> OIR EndpointValueRefBody
MapEndpointConstantV0(selected PIR constant) -> OIR EndpointConstantBody
MapEndpointPureNodeV0(selected PIR derived value) -> OIR EndpointPureNodeBody
```

Each mapping is a total function only on the exact supported source
constructors selected by Sections 2--10. It copies semantic operands after
authentication, rebases only the named local references, and rejects an
unknown source alternative. Equality of source and target encodings is never
used as the mapping law.

The role ABI mapping forms the exact OIR-local
`RoleEndpointAbiGraphBody`. Structural codecs map recursively after the
Interface codec DAG is admitted; General codecs retain their authenticated
declaration coordinate as an opaque target dependency. Slots, invocation
fibres, Statement aliases, transport edges, and completion variants are
filtered and rebased by the selectors below. No PIR Interface body is nested
in the OIR graph.

Codec child refs point backward. Fibres are nonempty, cover each invocation
target exactly once, and are in target order. ABI table order is the filtered
Interface-relative order; no duplicated numeric `order` field exists.

The endpoint spine and value-activity mapping form the OIR-local
`EndpointSpineEventBody`, `EndpointActivityBody`, and `EndpointActionBody`
constructors. The projector maps every supported source action explicitly;
Reduction and Terminal remain anchor-backed target tags, and an Oracle or
module occurrence has no mapping in this bounded profile.

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

Static FS mapping retains exact checked Fiat--Shamir frame coordinates while forming the
OIR-local `StaticFsEndpointSemanticsBody` and `EndpointChallengeLawBody`. The
OIR `EndpointDerivedPrefixLawBody` and
`EndpointChallengeTransitionLawBody` each have one selected tag; the source
projector may emit those tags only after the imported canonical-framed
construction laws have been authenticated and checked. The derived namespace
recipe is evaluated with a runtime draw ordinal and contains no stored
namespace datum.

Claim and anchor mapping forms the OIR-local `EndpointClaimAtomBody` and
`EndpointAnchoredObligationBody` tables. Nominal declaration references are
retained as opaque authenticated coordinates, while source claim, reduction,
publication, output, and terminal refs are rebased into their distinct target
namespaces. No source-owned enum body is copied by alias.

For every reduction, field 7 has exactly one row per declared output contract
in output-ordinal order. The row's claim sequence equals every and only local
claim atom whose source is that reduction and output ordinal, in `ClaimRef`
order; it may be empty or contain several refs because K2 does not assert a
one-claim-per-output law. The one FS interpretation-failure type is obtained
from the enclosing static construction. No per-challenge or protected-action
copy is admitted.

Plan mapping forms the OIR-local seven-table `PlanGraphBody`. It maps only
the selected reachable Plan closure, rebases every class-specific reference,
and preserves site qualification. `OracleValue` and `ModuleMove` have no
bounded target arm. Source `KeepState` maps to the absent OIR update value;
`ReplaceState` maps to the present arm. These are explicit constructor
mappings, not reuse of the PIR Plan body compiler.

The closed `EndpointValueRefBody` has no Plan arm, which prevents recursive
self-wrapping and keeps K2-owned positions Plan-free. Every decision spine ref
must name a Prover-message action, and every accepted-terminal ref must name an
exact `Accept` anchor. Recipe nodes are grouped first by the complete site body
and then by their owner-relative within-recipe order after reachable filtering.
Private-material, randomness, and state tables preserve filtered K3-B source
order. Move entries are strictly ascending by decision spine ref. Update
entries are strictly lexicographic by `(decision_spine_ref, state_ref)`.
Recipe-node order is strictly lexicographic by
`(site_body, within_recipe_ordinal)`. Derived exports are ordered by their
dense `PlanContinuationOutputRef`. Every table rejects
duplicate keys.
A recipe-node operand points backward to a node with the same exact site;
a move or update may reference only a node owned by its own decision. There is
exactly one move per decision spine and, for each selected state, exactly one
update per decision spine; `None` is K3-B `KeepState` and `Some` is
`ReplaceState`. Every
Plan edge is in range and the combined graph is acyclic under the admitted
decision/terminal schedule. A decision-site `PlanViewReadBody` must be the
exact rebased Plan-owner coordinate/value pair in that decision's admitted
`StrategyDecisionView`; a terminal-site read must satisfy the Plan owner's
exact guaranteed accepted-terminal read predicate. A terminal site has no move
or update, direct randomness is unavailable there, and every terminal node is
in the transitive closure of at least one selected same-site export.
`AcceptedTerminalPublicOutput` is legal only at a terminal site, its ordinal
must select an exact public output of that identical terminal anchor, and the
paired `EndpointValueRefBody` must be that output's exact value ref.

The one PIR-owned source-view domain body is exactly:

```text
EndpointSourceViewDomainBody(x) = R{
  0:EndpointPurposeBody(x.purpose),
  1:EndpointSemanticGraphBody(x.semantic_graph)
}
```

`PirEndpointSourceViewProfileId` directly imports the exact Interaction,
canonical-framed FS, Interface/Plan, and OIR endpoint-graph profiles. The OIR
profile's authenticated preimage owns every target constructor and
`EndpointContractLawV0`; the three PIR imports own every source declaration
the projector opens; and `DeriveEndpointContractV0` is OIR's evaluator. None
is an authored graph field. Family dispatch grants support only through the
exact canonical import rather than embedding a second profile-shaped body or
interpreting an unsupported family.

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
EndpointReadLawV0Body = V(0,U)
EndpointOwnerSchemaSetDomainBody = R{
  0:RootGrammarLawV0Body
}
EndpointReadManifestDomainBody(purpose) = R{
  0:EndpointPurposeBody(purpose),
  1:CR(EndpointOwnerSchemaSetId),
  2:EndpointReadLawV0Body
}
```

The selected `SemanticRegimeId` is already fixed by `B`, and the exact source-
view profile ID is already field 0 of K1 `ProfiledSemanticBody`. Neither value
is repeated inside these domain bodies. The source-view profile's authenticated
import closure and law source bind the selected owner grammar and read law.

`RootGrammarLawV0` has exactly five roots in tag order: admitted Protocol,
its exact admitted Core, the Protocol's exact admitted Construction, its exact
admitted Interface, and optional exact admitted Plan. Feature support
authenticates only the first four applicable roots and dispatches the
construction through `DispatchEndpointTranscriptConstruction` before any Plan
root is read. A Verifier request with a present Plan root is `Malformed`.
Either Plan-specialized Prover request with an absent Plan or absent exact
`CheckedPlanRealizes` preimage is `MissingDependency`; a present but
nonaffirmative owner result is `Refused`. A continuation request
also requires the owner-derived accepted-terminal arm map to contain at least
one nonempty arm. Protocol Fresh is traversable only far enough to return the
ordered unsupported result. Any unknown root,
field, variant, trailing field, sequence element grammar, atomic boundary, or
same-shaped body from another regime is a kind/regime failure, not an inert
coordinate.

The fixed evaluator recursively follows every field of the exact Appendix-A
owner bodies, including every option arm and every actual sequence element.
Traversal is depth-first in root-tag, record-field, variant-tag, and
sequence-index order. It emits one `OwnerCoordinateBody` for every typed atomic
boundary; the receipt retains the complete exact admitted subbody at that
boundary. There is no default or unknown arm. The selected Plan grammar change
rotates `PIRInterfacePlanProfileId`, the endpoint owner-schema/read-law
profiles, and their downstream exact-use chain while retaining the same
Foundation `SemanticRegimeId`. A policy or derivation-law change likewise
rotates its owning profile and downstream imports. Implementations
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
    V(0,U) | V(1,U) | V(2,U) | V(3,U) | V(4,U) | V(5,U)
// FreshEndpoint | GenericProverEndpoint | StandardOracleEndpoint
// ModuleEffectEndpoint | OtherTranscriptConstructionFamily
// NoPlanContinuationArm
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

| Owner path | Verifier FS | Plan-specialized Prover FS | Plan-continuation Prover FS |
|---|---|---|---|
| Protocol `.0 core_id` | Relevant Dependency/StaticFs | same | same |
| Protocol `.1 Fresh` | Unsupported Fresh | same | same |
| Protocol `.1 FS construction_id` | Relevant Dependency/StaticFs | same | same |
| Core `.0 used_modules` | role closure -> Dependency | same | same |
| Core `.1 public_inputs` | Relevant ABI/Type | same | same |
| Core `.2 verifier_private_inputs` | Relevant ABI/Type | Inert verifier-private | Inert verifier-private |
| Core `.3 constants` | role closure -> Constant/Type | same | same |
| Core `.4 derived_values` | role closure -> PureNode/Dependency/Type | same | same |
| Core `.5 scopes` | role closure -> Spine | same | role closure -> Spine; exact arm-path reads also Plan |
| Core `.6 bindings` | Relevant Spine/StaticFs | same | same |
| Core `.7 challenges` | Relevant Spine/StaticFs | same | same |
| Core `.8 oracles` | Unsupported Oracle | same | same |
| Core `.9 checks` | role closure -> Spine/Dependency/Type/PureNode | same | same |
| Core `.10 claims` | Relevant Claim/Anchor | same | same |
| Core `.11 reductions` | Relevant Spine/Anchor | same | same |
| Core `.12 terminals` | Relevant Spine/Anchor | same | Relevant Spine/Anchor/Plan for accepted-arm keys |
| Core `.13 occurrences` base cases `0..5` | role closure -> Spine plus dependency/value closure | same | same plus Plan for exact decision/terminal arm paths |
| Core `.13` Oracle/module cases `6..7` | Unsupported exact case | same | same |
| Construction fields `0..10` | Relevant StaticFs/Dependency/Type | same | same |
| Interface `.0 protocol_id` | Join-only Interface | same | same |
| Interface `.1..6` | exact Interface endpoint closure -> ABI; complement inert | same, with all completion entries in complement | same, with all completion entries in complement |
| Plan root absent | required by request formation | illegal for this purpose | illegal for this purpose |
| Plan `.0 protocol_id` | n/a | Join-only Plan | Join-only Plan |
| Plan `.1 private_material[*].key` | n/a | Inert private key | Inert private key |
| Plan `.1 private_material[*].kind/value_type` | n/a | reachable closure -> Plan/Type; complement dead | arm-extended reachable closure -> Plan/Type; complement dead |
| Plan `.2 randomness`, `.3 persistent_state` | n/a | reachable closure -> Plan/Type | arm-extended reachable closure -> Plan/Type |
| Plan `.4 decision_recipes` nodes/moves/updates | n/a | reachable decision closure -> Plan/Type; complement dead | reachable decision closure -> Plan/Type; complement dead |
| Plan `.5 derived_witness_exports[*].key` | n/a | Inert derived export | Inert derived export |
| Plan `.5 derived_witness_exports[*].source_site/value/value_type` | n/a | Inert derived export | selected exact arm export -> Plan/Type; complement inert derived export |
| Plan `.6 accepted_terminal_recipes[*].terminal_ref` | n/a | Inert dead Plan element | selected nonempty arm key -> Plan; complement dead |
| Plan `.6 accepted_terminal_recipes[*].nodes` | n/a | Inert dead Plan element | selected export-rooted site-local closure -> Plan/Type; complement dead |

The rows cover every current root field. Nested fields inherit the row's fixed
closure selector or its exact selected/complement result; there is no
most-specific-wins precedence. Current admitted Interface Oracle/module
targets are necessarily backed by the already-unsupported Core Oracle/module
case. A future Plan module constructor is a different owner grammar and fails
the pinned Plan-profile and endpoint-law join, while retaining the same
Foundation `SemanticRegimeId`, rather than inhabiting an unreachable current
`Unsupported` tag.

For every supported protocol owner row governed by `ProtocolRoleSemanticClosure`, each
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
2. `ProtocolRoleSemanticClosure` starts independently of the output graph. It seeds
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
3. `InterfaceEndpointReachableClosure` seeds public plus Verifier-private local
   invocation entries for the Verifier and public local invocation entries for
   the Prover; every Statement entry whose exact binding occurs in the spine;
   every transport entry whose exact target occurs in the spine and whose
   source/destination matches the exhaustive Section 8 role table; and all
   completion entries only for the Verifier. It then closes each selected use
   to its slot and each slot through the complete acyclic structural-codec
   child graph. It derives the exact selected/complement partition before
   rebasing.
4. `PurposeSelectedPlanReachableClosure` runs only after the feature-support
   phase has returned no reason. It always seeds each admitted decision move payload
   and each `ReplaceState` payload. For
   `PlanContinuationProverEndpoint`, it first derives
   `AcceptedPlanContinuationArmMap(P,plan)` from the exact admitted Protocol
   and the exact admitted Plan supplied by the affirmative extraction basis;
   its calls to `AcceptedPlanContinuationArm(P,plan,t)` supply that same pair.
   Absence of every nonempty arm is then the typed support result
   `Unsupported(NoPlanContinuationArm)`. It then also
   seeds every export named by a retained arm. The common worklist follows
   recipe operands, selected-state initializers, and node dependencies to
   private material, randomness, state, public view reads, and site-local
   recipe nodes. `KeepState` alone is not a seed; after a state is selected,
   its complete per-decision update row, including every `KeepState`, is
   retained. Node traversal is exact-site-local. A decision-derived export may
   enter an arm only when its decision is guaranteed active and ordered before
   that terminal; a terminal-derived export may enter only the arm keyed by
   its identical terminal. Every selected export receives one dense graph-
   local `PlanContinuationOutputRef`, and every retained arm refers only to
   those refs. For `PlanSpecializedProverEndpoint`, derived exports and
   accepted-terminal recipes are never seeds.

Each selector is bounded by the source body's already admitted K1 limits plus
the extraction visit limit. Duplicate visits do not duplicate receipts.
Selected receipts are sorted by exact owner coordinate body before comparison
with the view constructor's read set. Complement is the exact finite owner
domain minus selected. Any nonpartition, dangling edge, role disagreement, or
limit exhaustion produces no view.

<!-- zkc-profile-source:endpoint-source-view-semantics:end -->
