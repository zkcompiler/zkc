# OIR Endpoint and Projection Contract

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative endpoint-projection target
> **Provisional owner:** `oir`
> **Authority:** This page defines the bounded OIR semantic skeleton and
> PIR-to-OIR validation relation. It does not replace the current
> specifications under [`docs/`](../../docs/README.md), activate full Stage
> 4B, select final MLIR syntax, or make a cryptographic-security claim.

## 1. Selected factorization

The bounded profile accepts only the canonical-framed Fiat--Shamir family.
Every other authenticated construction family returns
`Unsupported(OtherTranscriptConstructionFamily)` before source extraction or
OIR construction. Duplex support needs a sibling endpoint profile that owns salt
placement, abstract proof-tuple parsing, prover-message wire codecs, and their
checked correspondence to distinct transcript encoders. None is inferred from
the canonical graph's namespaces, retry, or sampling-failure rows.

K3-D separates source support, source completeness, target validity, and
source-relative correctness:

```text
ClassifyEndpointProjectionSupport(exact admitted sources, purpose, profile)
  -> SupportedExtractionBasis | Unsupported | qualified noncompletion

ExtractEndpointSourceView(SupportedExtractionBasis, exact PIR evaluator)
  -> CheckedEndpointSourceView | qualified noncompletion

ConstructIndependentOirCandidate(exact SupportedExtractionBasis, OIR profile)
  -> unauthoritative OIR candidate | qualified noncompletion

AuthenticateAndAdmitOir(candidate, exact OIR dependencies)
  -> AdmittedOir | qualified nonadmission

FormProjectionProposition(CheckedEndpointSourceView, AdmittedOir, profile)
  -> FormedProjectionProposition

ValidateProjection(formed proposition, live authorities, checker, limits)
  -> Affirmative | Negative | qualified noncompletion
```

For the bounded profile, `SupportedExtractionBasis` contains the exact live
`CheckedProjectionOwnerAdapterV0` defined by the PIR source-view contract. The
adapter joins all currently available purpose-bound K2/K3-B owner views with
one explicitly admitted residual future-owner supplement; raw supplement
data, copied capabilities, or unauthenticated Interface/Plan facts cannot
enter either graph constructor. This is source-side authority only. Neither
the adapter nor the supplement is an input to source-blind local OIR
admission, and neither enters `OirId`.

The executable evidence exposes this target lane as
`project_supported_endpoint(basis)`. Source extraction and independent target
construction consume the identical live basis and adapter, while the target
lane receives no `CheckedEndpointSourceView` and performs no source/target
comparison. This makes the authority chain inspectable without putting a PIR
source ID, basis, adapter, or manifest into OIR semantic identity.

For the Prover, the supported family has two distinct purposes. The ordinary
`PlanSpecializedProverEndpoint(FiatShamir)` retains only public proof-message
decisions and their selected state. The
`PlanContinuationProverEndpoint(FiatShamir)` retains the same behavior plus
the complete site-qualified private-export closure promised by at least one
accepted-terminal continuation arm. A continuation request whose exact source
Plan yields no nonempty arm returns the typed source-support result
`Unsupported(NoPlanContinuationArm)` before source extraction or independent
target construction. It cannot fall through to an ordinary Prover target or
produce a partial OIR.

`LocalOirValid(O)` asks whether OIR is a coherent endpoint semantic object.
`ProjectionCorrect(S,O)` asks whether it is exactly the selected endpoint
meaning of the complete PIR-owned source view. Neither implies the other. A
locally valid target may omit a source check, alter one transcript coordinate,
or add an independently coherent action that causes the fixed law to derive an
extra requirement; it then remains locally valid but projection is Negative.

The producer establishes neither judgment. PIR derives source meaning, OIR
admits target meaning without source authority, and a third checker compares
them.

## 2. Why bounded v0 uses canonical equality

The previous draft used existential multi-plane correspondence maps. Cold
audit showed that those maps added failure modes while bounded K3-D admitted
none of the transformations that make a relation necessary: no semantic
reordering, effect split/fusion, pure-node optimization, ABI adaptation, or
Plan rewrite was supported.

K3-D therefore selects one canonical shared value schema:

```text
EndpointSemanticGraphBody
```

OIR is the one semantic owner and physical definition site for this bridge
schema and `DeriveEndpointContractV0`. PIR owns exhaustive source traversal,
the read manifest, and extraction into the OIR-owned value type. It may not
define or reinterpret a shadow graph schema. An exact schema or contract-law
change rotates the OIR language profile and every exact-used downstream PIR
projection-view profile. Producing this value transfers no source handle,
read authority, local OIR admission, or correctness.
Projection compares the independently formed canonical graph bodies exactly.

This is the minimum closed translation-validation boundary. It is stricter and
smaller than a general refinement relation, yet it preserves the decisive
separation between target validity and source correctness. A future optimizer,
rescheduler, split/fusion lowering, or ABI transformer must select a distinct
relation profile with exact rewrite laws and new falsification evidence. It
cannot weaken this profile in place.

<!-- zkc-profile-source:oir-endpoint-graph-semantics:start -->

## 3. Minimum semantic OIR

The complete bounded target identity is:

```text
OirEndpoint = {
  semantic_profile: OirEndpointGraphProfileId,
  semantic_graph: EndpointSemanticGraph
}
```

The exact graph schema and every target-local component body are defined
physically in Appendix A below. The grammar uses Foundation carriers for
typed content and declaration references, canonical values, value types, and
failure types, but it imports no PIR semantic-language profile. A foreign
reference is an opaque authenticated dependency until an operation governed
by another profile interprets it. The graph contains:

- role, exact-used dependencies, and exact value types;
- canonical constants and pure-node value graph;
- the slot-centric role ABI codec/slot/edge graph;
- exact total endpoint spine and K2 semantic frame coordinates;
- static canonical-framed Fiat--Shamir construction, prefix, namespace-recipe, retry, state,
  and failure laws;
- complete claim, reduction, publication, terminal, and closure graph;
- optional seven-table reachable Plan graph with site-qualified recipe nodes
  and derived exports.

For a Prover graph, the OIR-owned projection of reachable Plan meaning is
exactly:

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
```

The ordinary Plan-specialized purpose has an empty derived-export table. The
continuation purpose retains every and only export named by a nonempty
accepted-terminal arm and the complete export-rooted closure needed to derive
it. Recipe-node and export sites distinguish a decision spine ref from an
accepted-terminal ref; ordinal coincidence between those namespaces cannot
capture a node or value. The exact `PlanGraphBody` and all of its component
bodies are physically owned by OIR. PIR owns the source Plan and the checked
translation into this target grammar; another source language may form the
same target body without acquiring or imitating PIR authority.

Private continuation outputs have their own OIR access namespace:

```text
PrivatePlanContinuationAccess =
  PlanContinuationOutput(PlanContinuationOutputRef)
```

It is legal only while deriving or validating the private continuation
contract. It is not an `EndpointValueRef`, InteractiveCore value ref, role-ABI
value ref, public-closure ref, or ordinary Plan-move ref. In particular, the closed
`EndpointValueRefBody` gains no private-output arm.

The exact profile-owned `DeriveEndpointContractV0` evaluator derives one
closed `DerivedEndpointContractBody`: the complete static-obligation index,
the exact local-evaluator, counterparty, Plan-ingress, and storage
requirements, the static external completion interface, and the optional
terminal-indexed private Plan-continuation contract. These are exact semantic
consequences, not second authored graph tables. Local admission reruns the
evaluator and validates the complete body; a producer cannot add, omit, or
override one row or continuation-arm member.

The derived contract is not an execution trace. Runtime guard/activity,
draws, receipts, path-sensitive state versions, decoded values, transport
packaging, reached completion, and endpoint results remain Stage 4B subjects.
The identity-bearing graph nevertheless retains the complete K2 FS laws and
exact action/claim structure needed to define that later execution.

The OIR body contains no separate absence table. No ambient FS challenge
input, no Prover verifier-private read, no Prover external completion, and no
unclassified Plan read are formation laws over the complete graph and are
checked by local admission. It also contains no whole Protocol, Interface,
Plan, or source-view identity merely as provenance.

This body is the semantic skeleton, not final syntax. A later MLIR dialect may
have blocks, operations, attributes, and source locations, but local admission
must derive this exact semantic body before an `OirId` exists.

## 4. Identity

```text
OirId(endpoint) =
  ProfiledSemanticId<"oir.endpoint">(
    B, OirEndpointGraphProfileId,
    OirEndpointDomainBody(endpoint))
```

The carrier's `semantic_profile` must equal `OirEndpointGraphProfileId`. K1's
profiled wrapper places that ID in the semantic preimage exactly once; the
domain body does not repeat a profile body or profile ID.

`OirId` includes every semantic operand in the graph and excludes:

- full `ProtocolId`, `ProtocolInterfaceId`, or `ProverPlanId` when used only
  as origin;
- source-view ID, source maps, read manifest, or source authority;
- projector, checker, compiler, relation result, capability, or evidence;
- producer history, diagnostic, source location, display label, and cache;
- runtime invocation values, proof bytes, transcript receipts, sampled
  challenges, draw counts, deployment, or session identity.

An exact Core or TranscriptConstruction ID that K2 absorbs or uses in a
namespace remains inside the graph's dependency table. Original K2 scope,
binding, occurrence, challenge, condition, module-frame, and draw coordinates
remain wherever the selected K2 runtime law consumes them. Those values are
semantics, not provenance. Interface codec/slot and Plan table ordinals are
local graph refs and are rebased. The exact Interface codec content ID,
external slot key, and external Statement coordinate remain semantic graph
operands; rebasing may not erase or synthesize any of them.

Consequently, two exact sources with the same complete endpoint quotient share
one semantic OIR. For the ordinary Prover purpose, dead Plan nodes,
private-export-only declarations, and private source maps do not rotate it.
For the continuation purpose, every retained site-qualified node, derived
export, output ref, source site, type, path guarantee, and terminal-arm
membership is semantic: changing any of them rotates the graph/OIR or makes
reuse projection-negative. A reachable recipe, ABI edge, canonical-framed
Protocol coordinate, static FS law, Check, Reduction, Terminal, or any graph
operand
from which a requirement, external-completion, or private-continuation row is
derived has the same consequence. Equal private values or equal types never
identify distinct graph-local output refs.

`DerivedEndpointContractBody` is not copied into `OirEndpointDomainBody`, but
this does not make the law identity-inert. `OirEndpointGraphProfileId`
authenticates the exact `EndpointContractLawV0` declaration catalog. A change
to continuation-arm derivation, path guarantee, exact-use, atomicity, access
namespace, or contract body rotates that profile and therefore rotates
`OirId` even when the eleven graph fields happen to encode identically.

## 5. Independent local OIR admission

```text
AuthenticateOir(raw, exact OirSemanticBasis, dependency preimages)
  -> AuthenticatedOirCandidate

AdmitOir(authenticated candidate,
         exact OIR evaluator,
         total GeneralCodecAdmissionEvidenceMap,
         deterministic limits)
  -> QualifiedAdmission<AdmittedOir>
```

Local admission receives no source Protocol, Interface, Plan, source view,
manifest, source map, or projection claim. It checks:

1. exact K1 body shape, canonical encoding, ID, selected profile, basis, and
   regime;
2. sorted-unique direct graph-dependency and least-used type tables, no dead
   entry, and complete recursive live authentication of every referenced
   primitive/module/declaration/failure/codec-law preimage outside graph
   identity;
3. constant admission, pure-node ABI, bridge-profile canonical order,
   acyclicity, input availability, and the exact recursive public
   Check-reconstruction closure; for a Prover, every retained invocation target
   is Public and the source-independent `EndpointPublicClosureV0` classifies
   every retained local endpoint-value demand root and predecessor
   `StaticPublic` or
   `PublicHistory`. The graph-local transfer starts from Public invocation
   targets and typed constants, joins pure-node and public-computation
   predecessors, uses the fixed K2 transfers for messages/challenges/public
   presentations, and treats counterparty-only values as descriptive until an
   exact transport or public reconstruction makes them locally available.
   These roots include base/FS/anchor demands and the endpoint-value side of a
   Plan view read, but exclude private material, randomness, state, Plan
   recipe intermediates, and every private continuation-output ref. The latter
   is legal only in the disjoint `PrivatePlanContinuationAccess` namespace;
4. codec dependency order, slots, invocation fibres, Statement aliases,
   transports, completions, origin uniqueness, and role legality; for every
   local General codec ref, exact K3-B `DerivedExhaustive` or
   `CheckedCertificate` evidence and no other entry, with the corresponding
   law rerun under this OIR evaluator and limits;
5. rooted scope/opening/binding spine, exact K2 occurrence coordinates and
   total order, role ownership, guards, and stopping law;
6. exact K2 frame reconstruction, construction algorithm ABIs, dynamic
   per-draw namespace recipe, full-prefix law, squeeze length, state advance
   before accept, decode-after-accept, retry bound, exhaustion failure, and a
   total one-to-one Challenge-action/law index with exact original coordinates,
   output types, scope paths, joint predecessors, and the one global failure;
7. claim sources and usage; full reduction contract/scope/apply occurrence,
   ordered claims, side inputs, challenges, publication/next-challenge pairs,
   every output ordinal/contract and its complete matching claim-ref list;
   full terminal verdict, public outputs, required checks, required
   reductions, and terminal claims, with claim disposition derived from the
   verdict; then the finite K2 liveness, Last-Challenge,
   saturation, stopping, and linear-closure laws;
8. role shape and optional seven-table Plan closure: FS is present for both
   supported roles; Verifier requires Plan absent; Prover requires Plan
   present; every Prover-message action has exactly one Plan move and every
   Plan decision key resolves to such an action. Recipe nodes and derived
   exports carry an exact decision or accepted-terminal site; local node refs
   remain within that site; decision reads, moves, state updates, randomness
   availability, and action-spine refs are exact; accepted-terminal reads are
   derived constructor by constructor from the endpoint spine, scope, order,
   guard implication, and matching terminal output; terminal nodes are
   export-rooted; and every retained export has one exact site, value, and
   type. The ordinary Prover shape requires the derived-export table empty.
   The continuation shape requires at least one derived nonempty terminal arm
   and rejects any public-Plan-parameter declaration, operand, graph table, or
   requirement arm under this selected profile;
9. one total rerun of `DeriveEndpointContractV0`, including the complete
   `DerivedEndpointContractBody`: every exact static obligation; local-only
   evaluator ownership and the exact graph-only `EndpointValueAccessV0`
   least-fixed-point route/operand check; locally demanded pure-node closure;
   General-codec presentation paths; counterparty contracts;
   private-material/randomness ingress; state storage; exact Verifier
   completion interface; no semantic Prover completion; and, when present,
   the complete terminal-indexed private continuation contract. For every
   retained arm `t`, derivation emits exactly one
   `PlanContinuation(t)` obligation, resolves each dedicated private output
   access to one graph export, validates the same-terminal rule or the exact
   all-path decision-before-`t` guarantee, requires every and only qualifying
   export in output-ref order, and checks all-or-nothing arm issuance. Missing,
   extra, duplicate, dangling, cross-site, cross-graph, wrong-type, or unused
   exports fail; the four role/dataflow formation laws remain mandatory; and
10. cumulative K1 constitutional bounds for both the identity-bearing graph
    and the independently derived contract, plus explicit request-local work
    bounds; path-expansion oversize or exhaustion returns atomically with no
    partial contract.

Plan exact-use is purpose-specific and total. Ordinary Prover roots are moves
and state replacements. Continuation roots add every private output selected
by the derived nonempty terminal arms; closure then follows the output's exact
site-local value, recipe nodes, Plan reads, private ingress, randomness, and
state predecessors. Every retained Plan entry must be reached by the
applicable root set and every reached entry must be retained exactly once.
Local OIR admission derives this without a source handle. The projection
request separately requires the checked PIR source view whose owner-read
receipts and exact-use closure established the identical seven-table graph;
exact graph equality then prevents either side from omitting a source read or
inventing an ungrounded target entry.

The `PlanContinuation(t)` row is a static realization obligation only. It
states the exact `Accept` gate, sealed final-state input, export-rooted
terminal computation, path-guaranteed earlier decision exports, and atomic
membership that a later runtime must honor. Local OIR admission neither
reaches `t`, evaluates the arm, nor mints a private value or continuation
capability.

The one static FS failure is construction-wide. Every FS-failure completion
refers to it through the admitted construction and ABI; a challenge/action
cannot introduce a second identity. Runtime draw receipts and values are not
admission inputs.

`EndpointPublicClosureV0` imports K2's exact four-element `PCClass` lattice and
its exact `Join` and `Publish` functions. It reconstructs the applicable
scope-opening, binding, activity, effect, output, claim, reduction, and
terminal predecessor edges from the endpoint spine and anchors. Public
invocation targets and constants are `StaticPublic`; pure nodes, bindings,
guards, deterministic Verifier messages, Checks, reductions, and terminals use
`Join`; Prover messages use `Publish(activity)`; and a Challenge uses K2's
special public-condition and earlier-joint-member transfer. The bounded profile
has no Oracle or module arm. Missing edges, a Verifier-private predecessor, or
an invalid Challenge transfer fails local admission. This graph-local replay
does not claim equality with an original K2 node set; source extraction checks
that separate source-qualified fact before rebasing.

The General-codec evidence map is total over every and only General codec node
ref in the graph, in ref order, with exactly the K3-B `DerivedExhaustive` or
`CheckedCertificate` evidence for the resolved law; structural codec refs have
no entry. It is request-local admission input and does not enter `OirId`; cold
admission must obtain and rerun it. Certificate verification is admission-only
and never becomes a runtime endpoint requirement. Unknown syntax is
`Malformed`; a missing dependency, wrong typed axis,
unsupported OIR semantic profile, missing authority, policy refusal,
deterministic exhaustion, or evaluator failure retains its qualified result.
Only Affirmative mints `AdmittedOir`, establishing `LocalOirValid(O)` and
nothing source-relative.

<!-- zkc-profile-source:oir-endpoint-graph-semantics:end -->

<!-- zkc-profile-source:oir-projection-semantics:start -->

## 6. Semantic proposition and validation request

The proposition states only semantic meaning:

```text
ProjectionProposition = {
  purpose: EndpointProjectionPurpose,
  source_view_id: EndpointSourceViewId,
  target_oir_id: OirId,
  relation_profile: OirProjectionRelationProfileId
}

ProjectionPropositionId(x) =
  ProfiledSemanticId<"oir.projection-proposition">(
    B, OirProjectionRelationProfileId,
    ProjectionPropositionDomainBody(x))
```

Procedure, authority, and audit data remain outside it:

```text
ProjectionValidationRequest = {
  proposition,
  exact admitted Protocol,
  exact admitted ProtocolInterface,
  optional exact admitted ProverPlan,
  optional exact affirmative CheckedPlanRealizes,
  exact live CheckedProjectionOwnerAdapterV0,
  exact affirmative SupportedExtractionBasis,
  exact affirmative CheckedEndpointSourceView,
  exact AdmittedOir,
  exact checker basis and evaluator,
  deterministic limits
}
```

Request formation reauthenticates every named body and requires the live
adapter, owner-view capabilities, admitted residual supplement capability,
the exact identical `SupportedExtractionBasis`, the exact adapter retained by
the checked source view, and all other handles to agree with the proposition
IDs. The residual supplement is restricted to the closed families named by
the PIR source-view contract; it cannot override an available owner-issued
fact. Request formation and validation recompute source handles, schema-set
and manifest IDs, proposition ID, provenance, source label, checker basis, and
deterministic limit binding. Full source IDs, manifest, realized reads,
checker, limits, provenance, and evidence bind this request and the resulting
process-local capability, not proposition identity. View-equivalent distinct
sources may therefore share one proposition while receiving distinct live
capabilities.

The proposition purpose must equal the purpose inside the checked source-view
body, not merely have the same role. `PlanSpecializedProverEndpoint` requires
an empty site-qualified derived-export table and a derived private
continuation field of `None`. `PlanContinuationProverEndpoint` requires a
nonempty seven-table Plan closure, a derived `Some` contract containing at
least one nonempty terminal arm, and exactly one `PlanContinuation(t)` static
obligation per arm. This shape agreement is rederived from the admitted graph;
an authored contract, a same-role fallback, or an empty continuation target
cannot form the request.

There is no producer witness in this exact-equality profile. Removing it also
removes the earlier ambiguity between rejection of one witness and refutation
of an existential proposition.

## 7. Exact projection relation

Let `(source_profile,S)` be the authenticated profiled source subject retained
by the checked source capability, where `S` is its
`EndpointSourceViewDomainBody`. Let `(oir_profile,O)` be the independently
admitted profiled OIR subject, where `O` is its `OirEndpointDomainBody`.
For an admitted graph `G`, `ContractOf(G)` denotes the unique Affirmative
`DerivedEndpointContractBody` that local admission has already rederived;
qualified noncompletion cannot form an admitted OIR.
On the supported domain, `PurposeContractShape` is the closed predicate:

```text
VerifierEndpoint(FiatShamir) :=
  VerifierCompletions and private_plan_continuation = None
PlanSpecializedProverEndpoint(FiatShamir) :=
  NoSourceSemanticCompletion and private_plan_continuation = None
PlanContinuationProverEndpoint(FiatShamir) :=
  NoSourceSemanticCompletion and
  private_plan_continuation = Some(nonempty contract of nonempty arms)
```

It is false for every unsupported purpose/mode in this relation profile.
Bounded v0 defines:

```text
ProjectionCorrectV0((source_profile,S),(oir_profile,O)) :=
  source_profile = PirEndpointSourceViewProfileId
  and oir_profile = OirEndpointGraphProfileId
  and ContractLaw(source_profile) = EndpointContractLawV0
  and ContractLaw(oir_profile) = EndpointContractLawV0
  and PurposeRole(S.purpose) = O.semantic_graph.role
  and PurposeContractShape(
        S.purpose,
        ContractOf(O.semantic_graph))
  and M(S.semantic_graph) = M(O.semantic_graph)
```

The canonical encoder is injective, so byte equality here is exact typed graph
equality, not serialization coincidence. It covers every non-derived OIR
field at once: role, dependencies, types, constants, pure nodes, codec/slot
ABI, action spine/control order, static FS laws, claims, reduction/terminal
anchors, and the complete optional seven-table Plan, including every
site-qualified derived-export body.

The equality compares original K2 transcript coordinates literally. It
compares local graph refs only after each side independently satisfies the one
canonical construction and ordering law. It does not compare source maps,
whole source IDs, read receipts, or runtime FS receipts. Positive graph
equality supplies exact no-omission and no-phantom coverage for every table.
Both profile formations also rerun the same exact
`DeriveEndpointContractV0`, so equality of the base graph entails equality of
the complete `DerivedEndpointContractBody`: static obligations, exact
requirements, external completion interface, and the exact terminal-indexed
private continuation contract. This includes output refs, decision-or-terminal
source sites, result types, arm membership, the all-path guarantee for earlier
decision exports, and atomic membership. The dedicated private access is
resolved during derivation but never enters a generic endpoint-value plane.
No target universe can be silently omitted from a correspondence witness
because no such witness or partial plane exists. The four role/dataflow laws
in Section 3 are mandatory on both formed graphs and need no second projection
conjunct.

## 8. Outcomes and authority

The semantic Negative payload is closed and nonempty:

```text
ValidateProjection(request: ProjectionValidationRequest)
  -> ProjectionValidationOutcomeBody

EndpointGraphFieldBody =
    V(0,U) | V(1,U) | V(2,U) | V(3,U) | V(4,U) | V(5,U)
  | V(6,U) | V(7,U) | V(8,U) | V(9,U) | V(10,U)
// Role | Dependencies | ValueTypes | Constants | PureNodes | RoleAbi
// Spine | StaticFs | Claims | AnchoredObligations | OptionalPlan

CompleteExactGraphMismatchBody =
  S[EndpointGraphFieldBody... in increasing tag order, nonempty]

ProjectionValidationOutcomeBody =
    V(0,U)
  | V(1,CompleteExactGraphMismatchBody)
  | V(2,U) | V(3,U) | V(4,U)
  | V(5,U) | V(6,U) | V(7,U)
// Affirmative | Negative | MissingDependency | KindMismatch | Malformed
// Refused | DeterministicLimitExceeded | CheckerFailure
```

A Negative payload contains every and only top-level graph-field tag whose
canonical field body differs. Detailed recursive differences may accompany the
result as non-authoritative diagnostics but cannot change it. Purpose/role,
profile, kind, and authority disagreement is rejected during request formation
as the corresponding qualified branch; it is not disguised as graph
inequality.

For a well-formed, support-marked, fully joined proposition, exact graph
comparison is a complete decider. `Negative` is therefore a completed semantic
answer, not verifier rejection. The unit payloads on qualified branches are
intentional: exact diagnostic coordinates are not semantic API in bounded
K3-D. Missing bytes, types, authority, formation, limits, and evaluator
operation cannot become Negative, and no partial target or comparison result
is returned.

A convenience pipeline may retain an optional result for each sequential
stage. If an earlier stage does not affirm, every later stage is
`NotAttempted` process state represented by absence, not a fabricated
`Refused`, `Negative`, or other semantic outcome. `NotAttempted` is therefore
not a member of `ProjectionValidationOutcomeBody`.

Only Affirmative mints:

```text
ProjectedOirCapability<exact ProjectionValidationRequest>
```

The capability is opaque, linear where consumed, process-local, and bound to
the exact identical live validation request and therefore to its full basis,
adapter, source, proposition, and target chain. Every consumed carrier in that
chain is process-registered and noncopyable; a structurally equal
reconstruction is not authority even when all public fields match.
Serialization transfers neither it nor authority. Cold recovery
reauthenticates and readmits every subject, reclassifies support, re-extracts
the source view, readmits OIR, reforms the request, and reruns validation.

## 9. Role semantics and deferred endpoint pairing

For FS, both roles derive the same challenges locally from identical static
transcript semantics. A challenge is never ambient input. Every and only
Interface-declared `PublicDerivation -> ExternalApplication` export appears in
the Verifier ABI; cardinality is `0..n`. The Prover keeps the same derivation
internal.

The Verifier owns Checks, Reduction application, Terminal semantics, the
Protocol verdict, and every applicable completion presentation. The Prover
owns proof-message production and its reachable Plan but has
`NoSourceSemanticCompletion` under both supported Prover purposes. The
continuation purpose adds a disjoint static private Plan-continuation contract;
it does not add an Interface completion, a public transport, or a Prover
Protocol verdict. InteractiveCore strategy `Stop`, unavailable authority,
private search exhaustion, accepted-terminal finalization failure, and runtime
FS exhaustion remain
execution outcomes rather than static completion claims.

K3-D deliberately does **not** define an authoritative source-independent
pair judgment over two admitted OIRs. A first candidate attempted to compare
role-neutral public graphs and role-dual edge surfaces. Falsification showed
that this is a distinct semantic layer: it needs exact canonical normalized
surface bodies, total ref rebasing, transport and action-duality tables, a
complete mismatch partition, and independent output-size and work bounds.
Leaving any of those rules implicit would allow two conforming checkers to
disagree while claiming the same pair profile.

Nor may K3-D obtain pair authority by asking whether two endpoint projections
share one source tuple. That question is useful as a consistency check, but
its negative branch is uninhabited after two affirmative exact projections and
therefore cannot establish compatibility of independently supplied targets.

The authoritative K3-D boundary consequently ends at two separate judgments:

1. source-blind `LocalOirValid(O)` for each endpoint; and
2. source-relative `ProjectionCorrect(S,O)` for each independently formed
   source-view/OIR pair.

A bounded fixture may compare a Verifier and Prover graph as a
non-authoritative pressure probe. Such a comparison mints no proposition,
semantic Negative, or capability and is not part of K3-D closure evidence.

The Stage 4B OIR owner may activate target-only endpoint pairing only after it
defines all of the following together:

- exact canonical common-surface and role-edge bodies, including every element
  body, table order, root set, dense-rebase rule, and recursively expanded
  codec body;
- a total transport, action, Plan, counterparty, export, and completion
  duality algorithm;
- a closed, exhaustive mismatch partition whose tag predicates are exact and
  may overlap when one defect violates several conjuncts;
- pair-local K1 encoded-byte, node, child-edge, and depth preflight plus an
  explicit request work bound, with atomic qualified noncompletion; and
- an exact authority and cold-recovery contract independent of source
  projection capabilities.

This deferral does not weaken either endpoint's static FS semantics or its
source-relative projection. It only refuses to turn an underdefined
cross-target normalization into semantic authority. Pairing asserts no
liveness, Prover success, proof acceptance, relation satisfaction, or
cryptographic property even after that later contract exists.

## 10. Support boundary

| Source/purpose | `EndpointProjectionSemanticsV0` result |
|---|---|
| Canonical-framed FS Verifier over base non-Oracle, non-module effects | Supported |
| Canonical-framed FS Plan-specialized Prover over base Plan recipes | Supported |
| Canonical-framed FS Plan-continuation Prover with one or more owner-derived nonempty accepted-terminal arms | Supported |
| Plan-continuation Prover whose exact Plan yields no nonempty accepted-terminal arm | `Unsupported(NoPlanContinuationArm)` |
| Any noncanonical authenticated transcript-construction family, including duplex-sponge | `Unsupported(OtherTranscriptConstructionFamily)` |
| Fresh Verifier or Prover | `Unsupported(FreshEndpoint)` |
| Generic Plan-free Prover | `Unsupported(GenericProverEndpoint)` |
| Core with a native Oracle declaration or occurrence | `Unsupported(StandardOracleEndpoint)` |
| Any admitted module effect | `Unsupported(ModuleEffectEndpoint)` |
| Interface/Plan grammar containing a public Plan-parameter lane or module recipe | Fails the selected profile/schema join; not classifiable under the selected endpoint-projection profile |
| Legacy carrier lacking a supported K2 effect law | Stops at PIR admission |

The table is exhaustive for the closed purpose grammar and selected PIR/Plan
profile. A new source case or purpose rotates the profile and adds an explicit
disposition before extraction can run.

## 11. Execution and Realization boundary

K3-D closes endpoint semantic identity, the derived static contract, and
source-relative projection; it does not activate full OIR execution. Stage 4B
may define an abstract execution relation over role inputs, counterparty
values, and explicit capabilities for graph requirements. That relation owns
runtime presence, path-sensitive state, draw instances, decoded values,
traces, reached completion, and qualified noncompletion. It must interpret
the exact admitted graph rather than add an ambient source read.

Concrete memory, scheduling, libraries, devices, services, credentials,
deployment, and invocation authority belong to Realization. Reachable base
Plan semantics has already entered the Prover graph; concrete suppliers never
did. There is no implicit `BelowOirPlanBasis` branch.

Runtime private continuation remains unactivated. PIR Plan owns generation,
the sealed post-generation state, the one-use accepted-terminal continuation
right, export evaluation, and atomic issuance of the reached arm. The static
OIR contract neither consumes that live right nor projects its private values.
A later Realization design must define the exact runtime binding from an
admitted continuation OIR and its `PlanContinuation(t)` obligation to the
identical PIR Plan session/capability chain before any runtime continuation
projection can be claimed. An inactive terminal arm is absence, not an empty
tuple, and a failed issuance returns no prefix or subset.

Projection performs no arithmetization, polynomial-commitment selection,
batching, recursion, IOP compilation, or Fiat--Shamir conversion. Such a
transformation first needs its own admitted semantic target and checked
source/target relation.

## 12. Reopen rules and non-claims

The accepted-terminal continuation extension rotates the selected
`PIRInterfacePlanProfileId`, `OirEndpointGraphProfileId`,
`PirEndpointSourceViewProfileId`, and `OirProjectionRelationProfileId`, plus
every identity formed under those profiles. It does not rotate Foundation `SemanticRegimeId`, Foundation
semantic-language meaning, InteractiveCore or Fiat--Shamir construction
profiles, `CoreId`, or `ProtocolId`. Old profile bodies may
be retained as historical evidence but cannot authenticate this grammar.

The endpoint-projection contract had already been reopened locally to retain
Protocol framing coordinates, replace a static namespace datum with the
per-draw recipe, preserve the
complete slot graph and claim/reduction/terminal structure, and replace
incomplete correspondence planes with total canonical equality. This
continuation addition reopens only the dependent Interface/Plan and endpoint
profiles needed to represent the selected Plan meaning; it does not reinterpret
old bytes under a new semantic regime.

Reopen this exact-equality profile again only when a concrete supported endpoint
needs semantic reordering, optimization, split/fusion, ABI adaptation, or
another meaning-preserving nonidentity relation. Reopen K2 or K3-B only when a
positive endpoint inhabitant needs a source-owned fact their current exact
schemas cannot express.

The bounded executable instrument is a falsifier for this contract, not a
formal proof, complete OIR implementation, compiler-correctness theorem,
family-wide projectability result, or security claim.

<!-- zkc-profile-source:oir-projection-semantics:end -->

## Appendix A. Exact OIR and projection bodies

All bodies use the exact Foundation content-reference notation and the selected
`PriorMetaAuthenticationBasis` and `SemanticRegimeId`.
`CR(x)=Y(ContentRefV0(x))`, `DR(x)=DeclarationRefBody(x)`,
`VT(T)=CanonicalValueTypeBody(T)`,
`FT(f)=CanonicalSemanticFailureTypeBody(f)`, and
`DV(T,v)=v.datum` after exact Foundation admission. OIR owns every endpoint
body in this appendix. `CR` and `DR` preserve typed foreign coordinates as
opaque authenticated dependencies; their presence does not import a foreign
semantic-language profile or authorize OIR to interpret the referenced
declaration. Sets sort by complete encoded body bytes and reject duplicates.
Sequences preserve the stated order, and sequence position is the local
reference unless stated otherwise.

<!-- zkc-profile-source:oir-endpoint-graph-bodies:start -->

```text
EndpointChallengeModeBody = V(0,U) | V(1,U)
// Fresh | FiatShamir
EndpointPurposeBody =
    V(0,EndpointChallengeModeBody) | V(1,EndpointChallengeModeBody)
  | V(2,EndpointChallengeModeBody) | V(3,EndpointChallengeModeBody)
// VerifierEndpoint | GenericProverEndpoint | PlanSpecializedProverEndpoint
// PlanContinuationProverEndpoint
EndpointRoleBody = V(0,U) | V(1,U)
// Verifier | Prover
EndpointOptionBody(None,F) = V(0,U)
EndpointOptionBody(Some(x),F) = V(1,F(x))

EndpointPublicBindingClassBody = V(0,U) | V(1,U) | V(2,U)
EndpointCoinCorrelationBody =
    V(0,U)
  | V(1,R{0:DR(group),1:N(index),2:S[N(prior_challenge_ref)...]})
EndpointReductionUsePolicyBody = V(0,U) | V(1,DR(sharing_contract))
EndpointClaimUsageBody = V(0,U) | V(1,U)
EndpointTerminalVerdictBody = V(0,U) | V(1,U) | V(2,U)
EndpointTransportActorBody = V(0,U) | V(1,U) | V(2,U)
EndpointTransportDestinationBody = V(0,U) | V(1,U) | V(2,U)
EndpointPrivateMaterialKindBody = V(0,U) | V(1,U) | V(2,U)

EndpointDependencyBody =
    V(0,CR(core_id)) | V(1,CR(construction_id))
  | V(2,CR(algorithm_id)) | V(3,CR(evaluation_contract_id))
  | V(4,CR(semantic_module_id))

EndpointValueRefBody =
    V(0,N(invocation_target_ref))
  | V(1,N(constant_ref))
  | V(2,N(pure_node_ref))
  | V(3,R{0:N(spine_event_ref),1:N(output_ordinal)})

EndpointConstantBody(x) = R{
  0:N(type_ref),1:DV(type_table[type_ref],x.value)
}
EndpointPureNodeBody(x) = R{
  0:N(algorithm_dependency),1:N(evaluation_dependency),
  2:S[EndpointValueRefBody(input)...],3:N(result_type_ref)
}

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
  1:V(0,EndpointStructuralCodecBody(x)) | V(1,DR(x.general_codec_law))
}
EndpointSlotBody(x) = R{0:Q(x.external_key),1:N(x.codec_ref)}
EndpointInvocationClassBody = V(0,U) | V(1,U)
// PublicInput | VerifierPrivateInput
EndpointInvocationTargetBody(x) = R{
  0:EndpointInvocationClassBody(x.class),1:N(x.type_ref)
}
EndpointInvocationFibreBody(x) = R{
  0:N(x.slot_ref),1:S[N(invocation_target_ref)...]
}
EndpointStatementFlowBody = V(0,N(invocation_target_ref)) | V(1,U)
// SuppliesInvocation | ExposesOpenedBinding
EndpointStatementAliasBody(x) = R{
  0:Q(x.external_statement),1:N(x.slot_ref),2:N(x.binding_spine_ref),
  3:EndpointStatementFlowBody(x.flow)
}
EndpointTransportEdgeBody(x) = R{
  0:N(x.target_spine_ref),1:EndpointTransportActorBody(x.source),
  2:EndpointTransportDestinationBody(x.destination),3:N(x.slot_ref)
}
EndpointCompletionTargetBody = V(0,N(terminal_spine_ref)) | V(1,U)
EndpointCompletionCoordinateBody =
    V(0,R{0:N(terminal_spine_ref),1:N(output_ordinal)})
  | V(1,U) | V(2,U) | V(3,U) | V(4,U) | V(5,U) | V(6,U)
EndpointCompletionVariantBody(x) = R{
  0:EndpointCompletionTargetBody(x.target),1:Q(x.external_tag),
  2:S[R{0:EndpointCompletionCoordinateBody(coordinate),
        1:N(slot_ref)}... in coordinate-body order]
}
RoleEndpointAbiGraphBody(x) = R{
  0:S[EndpointCodecNodeBody...],1:S[EndpointSlotBody...],
  2:S[EndpointInvocationTargetBody...],3:S[EndpointInvocationFibreBody...],
  4:S[EndpointStatementAliasBody...],5:S[EndpointTransportEdgeBody...],
  6:S[EndpointCompletionVariantBody...]
}

EndpointActivityBody = V(0,U)
  | V(1,R{0:N(algorithm_dependency),1:N(evaluation_dependency),
          2:S[EndpointValueRefBody(input)...]})
// Always | Guarded
EndpointScopeOpeningBody = V(0,U) | V(1,N(original_occurrence_ordinal))
EndpointMessageActionBody(x) = R{0:DR(channel),1:N(result_type_ref)}
EndpointVerifierMessageActionBody(x) = R{
  0:DR(channel),1:N(algorithm_dependency),2:N(evaluation_dependency),
  3:S[EndpointValueRefBody(input)...],4:N(result_type_ref)
}
EndpointChallengeActionBody(x) = R{0:N(challenge_law_ref)}
EndpointCheckActionBody(x) = R{
  0:N(algorithm_dependency),1:N(evaluation_dependency),
  2:S[EndpointValueRefBody(input)...],3:N(boolean_result_type_ref)
}
EndpointActionBody =
    V(0,EndpointMessageActionBody)
  | V(1,EndpointVerifierMessageActionBody)
  | V(2,EndpointChallengeActionBody)
  | V(3,EndpointCheckActionBody)
  | V(4,U) | V(5,U)
EndpointSpineEventBody =
    V(0,U)
  | V(1,R{0:S[N(original_scope_ordinal)...],
          1:EndpointOptionBody(parent_scope_event_ref,N),
          2:EndpointScopeOpeningBody(opening)})
  | V(2,R{0:N(original_binding_ordinal),1:N(scope_event_ref),
          2:EndpointPublicBindingClassBody(class),
          3:EndpointValueRefBody(value)})
  | V(3,R{0:N(original_occurrence_ordinal),1:N(scope_event_ref),
          2:EndpointActivityBody(activity),3:EndpointActionBody(action)})

EndpointChallengeLawBody(x) = R{
  0:N(original_challenge_ordinal),1:N(value_type_ref),
  2:DR(domain),3:DR(fresh_law),
  4:EndpointCoinCorrelationBody(correlation),
  5:EndpointReductionUsePolicyBody(reduction_use),
  6:S[EndpointValueRefBody(condition)...],
  7:N(draw_bytes),8:N(maximum_draws),
  9:N(accept_algorithm_dependency),10:N(accept_evaluation_dependency),
 11:N(decode_algorithm_dependency),12:N(decode_evaluation_dependency)
}
EndpointDerivedPrefixLawBody = V(0,U)
EndpointChallengeTransitionLawBody = V(0,U)
StaticFsEndpointSemanticsBody(x) = R{
  0:N(core_dependency),1:N(construction_dependency),
  2:N(state_type_ref),3:N(bytes_type_ref),4:N(natural_type_ref),
  5:DV(type_table[state_type_ref],initial_state),
  6:N(absorb_algorithm_dependency),7:N(absorb_evaluation_dependency),
  8:N(squeeze_algorithm_dependency),9:N(squeeze_evaluation_dependency),
 10:N(advance_algorithm_dependency),11:N(advance_evaluation_dependency),
 12:DR(application_domain),13:FT(sampling_exhausted_failure),
 14:EndpointDerivedPrefixLawBody,15:EndpointChallengeTransitionLawBody,
 16:S[EndpointChallengeLawBody(rule)...]
}

EndpointClaimSourceBody = V(0,N(binding_spine_ref))
  | V(1,R{0:N(reduction_spine_ref),1:N(output_ordinal)})
EndpointClaimAtomBody(x) = R{
  0:DR(contract),1:EndpointClaimUsageBody(usage),
  2:N(scope_event_ref),3:EndpointClaimSourceBody(source)
}
EndpointReductionPublicationBody(x) = R{
  0:N(publication_spine_ref),
  1:EndpointOptionBody(next_challenge_law_ref,N)
}
EndpointReductionOutputClaimBody(x) = R{
  0:N(output_ordinal),1:DR(contract),
  2:S[N(output_claim_ref)... in claim-ref order]
}
EndpointAnchoredObligationBody =
    V(0,R{
      0:DR(contract),1:N(scope_event_ref),2:N(apply_spine_ref),
      3:S[N(input_claim_ref)...],4:S[EndpointValueRefBody(side_input)...],
      5:S[N(required_challenge_law_ref)...],
      6:S[EndpointReductionPublicationBody(requirement)...],
      7:S[EndpointReductionOutputClaimBody(output)...]
    })
  | V(1,R{
      0:N(terminal_spine_ref),1:EndpointTerminalVerdictBody(verdict),
      2:S[EndpointValueRefBody(public_output)...],
      3:S[N(required_check_spine_ref)... ascending, no repeat],
      4:S[N(required_reduction_spine_ref)... ascending, no repeat],
      5:S[N(terminal_claim_ref)... ascending, no repeat]
    })

PlanValueRefBody =
    V(0,N(private_material_ref)) | V(1,N(randomness_ref))
  | V(2,N(state_ref)) | V(3,N(recipe_node_ref))
  | V(4,PlanViewReadBody(read))
  | V(5,R{0:N(type_ref),1:DV(type_table[type_ref],value)})
PlanViewCoordinateBody =
    V(0,N(constant_ref)) | V(1,N(invocation_target_ref))
  | V(2,N(binding_spine_ref)) | V(3,N(message_spine_ref))
  | V(4,N(challenge_spine_ref)) | V(5,N(prior_decision_spine_ref))
  | V(6,N(accepted_terminal_public_output_ordinal))
PlanViewReadBody(x) = R{
  0:PlanViewCoordinateBody(x.coordinate),1:EndpointValueRefBody(x.value)
}
PlanInitializerBody = V(0,N(private_material_ref))
  | V(1,R{0:N(type_ref),1:DV(type_table[type_ref],value)})
PlanPrivateMaterialBody = R{
  0:EndpointPrivateMaterialKindBody(kind),1:N(type_ref)
}
PlanRandomnessBody = R{
  0:N(type_ref),1:N(first_available_decision_spine_ref)
}
PlanStateBody = R{0:N(type_ref),1:PlanInitializerBody(initializer)}
PlanRecipeNodeSiteBody = V(0,N(decision_spine_ref))
  | V(1,N(accepted_terminal_ref))
PlanGraphRecipeNodeBody = R{
  0:PlanRecipeNodeSiteBody(site),
  1:N(algorithm_dependency),2:N(evaluation_dependency),
  3:S[PlanValueRefBody(input)...],4:N(result_type_ref)
}
PlanMoveBody = V(0,PlanValueRefBody)
PlanMoveEntryBody = R{0:N(decision_spine_ref),1:PlanMoveBody(move)}
PlanUpdateBody = R{
  0:N(decision_spine_ref),1:N(state_ref),
  2:EndpointOptionBody(value,PlanValueRefBody)
}
PlanGraphDerivedExportBody = R{
  0:PlanRecipeNodeSiteBody(source_site),
  1:PlanValueRefBody(value),2:N(result_type_ref)
}
PlanGraphBody(x) = R{
  0:S[PlanPrivateMaterialBody...],1:S[PlanRandomnessBody...],
  2:S[PlanStateBody...],
  3:S[PlanGraphRecipeNodeBody... in site/within-site order],
  4:S[PlanMoveEntryBody...],5:S[PlanUpdateBody...],
  6:S[PlanGraphDerivedExportBody... in output-ref order]
}

EndpointContractLawV0Body = V(0,U)

EndpointSemanticGraphBody(x) = R{
  0:EndpointRoleBody(x.role),
  1:S[EndpointDependencyBody(d)... in body-byte order],
  2:S[VT(T)... in body-byte order],
  3:S[EndpointConstantBody...],4:S[EndpointPureNodeBody...],
  5:RoleEndpointAbiGraphBody(x.abi),
  6:S[EndpointSpineEventBody...],
  7:EndpointOptionBody(x.fs,StaticFsEndpointSemanticsBody),
  8:S[EndpointClaimAtomBody...],
  9:S[EndpointAnchoredObligationBody...],
 10:EndpointOptionBody(x.plan,PlanGraphBody)
}

OirEndpointDomainBody(x) = EndpointSemanticGraphBody(x.semantic_graph)
```

The target-local enums above preserve endpoint meaning, not a source body's
encoding by alias. The PIR projector has an explicit total mapping from each
supported source constructor into these tags. A source enum extension is
therefore unsupported until that mapping and the source-view profile rotate;
it cannot silently acquire an OIR tag. Conversely, changing a target tag or
field rotates only the OIR graph profile and its exact downstream closure.

<!-- zkc-profile-source:oir-endpoint-graph-bodies:end -->

<!-- zkc-profile-source:oir-endpoint-contract-law:start -->

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
  | V(6,N(accepted_terminal_ref))
// SlotIngress | PlanDecision | TranscriptFrame | LocalOccurrence
// ChallengeInterpret | Presentation | PlanContinuation

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
  | V(9,R{0:PlanRecipeNodeSiteBody,
          1:N(plan_recipe_node_ref)})
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
          1:EndpointPrivateMaterialKindBody(kind),2:N(type_ref)})
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

PrivatePlanContinuationAccessBody =
  V(0,N(plan_continuation_output_ref))
// PlanContinuationOutput; legal only inside the private continuation contract

PlanContinuationOutputDeclBody(x) = R{
  0:PrivatePlanContinuationAccessBody(
      PlanContinuationOutput(x.output_ref)),
  1:PlanRecipeNodeSiteBody(x.source_site),
  2:N(x.type_ref)
}

AcceptedPlanContinuationArmDeclBody(x) = R{
  0:N(x.accepted_terminal_ref),
  1:S[PlanContinuationOutputDeclBody(output)... in output-ref order]
}

PrivatePlanContinuationContractBody(x) =
  S[AcceptedPlanContinuationArmDeclBody(arm)... in terminal-ref order]

DerivedEndpointContractBody(x) = R{
  0:S[EndpointStaticObligationBody... in full-body byte order],
  1:S[OirRequirementBody... in full-body byte order],
  2:EndpointCompletionInterfaceBody(x.completion_interface),
  3:EndpointOptionBody(
      x.private_plan_continuation,
      PrivatePlanContinuationContractBody)
}

EndpointContractDerivationOutcomeBody =
    V(0,DerivedEndpointContractBody)
  | V(1,U) | V(2,U) | V(3,U) | V(4,U) | V(5,U) | V(6,U)
// Affirmative | MissingDependency | KindMismatch | Malformed | Refused
// DeterministicLimitExceeded | CheckerFailure

```

`DeriveEndpointContractV0` applies the following exact continuation law. The
ordinary Plan-specialized graph has no retained derived export and yields
`private_plan_continuation = None`. A continuation graph yields `Some` with a
nonempty terminal-ordered sequence of nonempty arms. For each admitted
`Accept` terminal `t`, the arm contains every and only retained decision-site
export whose source decision is guaranteed active and ordered before `t` on
every `t`-reaching path, plus every and only retained accepted-terminal export
whose site is exactly `t`. An arm with no such export is absent. One
decision-site output ref may occur in several arms when each path guarantee
holds; a terminal-site output ref may occur only in its own arm. Within one
arm, output refs are strictly ordered and unique.

PIR source support and extraction obtain that selection only by calling the
Plan-owned `AcceptedPlanContinuationArm(P,plan,t)` law and the PIR source-
view-owned `AcceptedPlanContinuationArmMap(P,plan)` law with the exact admitted
Protocol and exact admitted Plan in the extraction basis. There is no
protocol-only or ambient-Plan overload. Source-blind OIR admission does not
call those PIR functions or receive `P` or `plan`; it independently derives
the corresponding graph-local arm law from the complete candidate graph and
rejects any mismatch. Projection compares the two canonical graphs exactly;
the one shared `DeriveEndpointContractV0` law then entails equality of their
derived contracts without adding a second contract-comparison field.

Every output access resolves by its dedicated ref to exactly one entry in the
imported `site_qualified_derived_exports` table. The declaration's site and
type must equal that entry exactly. Every retained export occurs in at least
one derived arm, every arm member resolves to a retained export, every retained
terminal recipe node is reached from one of its terminal exports, and every
resulting Plan entry is exact-used by the applicable ordinary or continuation
root closure. Lookup by terminal/type pair, value equality, source witness key,
or an `EndpointValueRefBody` is forbidden.

The obligation sequence contains exactly one `V(6,N(t))` row per retained
arm. That row binds the `Accept` gate, sealed final-state source, exact
export-rooted terminal evaluation, all decision-path guarantees, and atomic
all-or-nothing membership for `t`. The external completion body remains
`V(1,U)` (`NoSourceSemanticCompletion`) for either Prover purpose. The
selected `OirRequirementBody` has exactly the five arms shown above: it has no
public Plan-parameter ingress. `EndpointContractDerivationOutcomeBody` has no
`Unsupported` arm; `Unsupported(NoPlanContinuationArm)` is decided by source
support classification before an OIR candidate exists.

The direct Plan-owned next-ingress handoff has no `EndpointValueRef`, no OIR
runtime operation or runtime value, and no serialized capability. This OIR
contract is static only. Reaching an accepted terminal, atomically producing
its private continuation arm, and issuing a live right remain PIR Plan-runtime
authority; an eventual runtime OIR design must introduce a distinct checked
boundary rather than reinterpret this contract as an executable handoff.

<!-- zkc-profile-source:oir-endpoint-contract-law:end -->

<!-- zkc-profile-source:oir-projection-body:start -->

```text
ProjectionPropositionDomainBody(x) = R{
  0:EndpointPurposeBody(x.purpose),
  1:CR(x.source_view_id),
  2:CR(x.target_oir_id)
}
```

The semantic proposition domain has exactly three fields. Its exact relation
profile is field 0 of the outer K1 `ProfiledSemanticBody`, not a fourth domain
field. Source IDs, manifest, source maps, read receipts,
support/extraction/admission capabilities, checker, limits, evidence, and
provenance are request inputs and cannot appear in this body. K3-D defines no
pair proposition body.

`ProjectionValidationRequest` and its checker coordinate are live operation
records under `OirProjectionRelationProfileId`; neither is a profiled semantic
subject. The request contains process authority, limits, provenance, and a
source label, is noncopyable and nonserializable, and is valid only while the
identical bearers remain live. An implementation may compute an inert
diagnostic fingerprint over its public fields, but that fingerprint grants no
authority, cannot reconstruct the request, and is absent from every semantic
preimage. A future portable projection certificate would require a new
semantic subject and profile with its own exact body and evidence law; it
cannot promote this live request or its diagnostic fingerprint by convention.

The OIR body must fit the cumulative K1 `2^20` encoded-byte, `2^14` node,
`2^14` aggregate-child-edge, and depth-384 limits. Local admission and
projection each also receive an explicit request-local work limit at most
`2^17`. Exhaustion is atomic and cannot be converted into Negative.

<!-- zkc-profile-source:oir-projection-body:end -->
