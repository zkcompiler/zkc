# OIR Endpoint and Projection Contract

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative K3-D target
> **Provisional owner:** `oir`
> **Authority:** This page defines the bounded K3-D OIR semantic skeleton and
> PIR-to-OIR validation relation. It does not replace the current
> specifications under [`docs/`](../../docs/README.md), activate full Stage
> 4B, select final MLIR syntax, or make a cryptographic-security claim.

## 1. Selected factorization

K3-D separates source support, source completeness, target validity, and
source-relative correctness:

```text
ClassifyEndpointProjectionSupport(exact admitted sources, purpose, profile)
  -> SupportedExtractionBasis | Unsupported | qualified noncompletion

ExtractEndpointSourceView(SupportedExtractionBasis, exact PIR evaluator)
  -> CheckedEndpointSourceView | Negative adequacy | qualified noncompletion

ProjectEndpoint(CheckedEndpointSourceView)
  -> unauthoritative OIR candidate | qualified noncompletion

AuthenticateAndAdmitOir(candidate, exact OIR dependencies)
  -> AdmittedOir | qualified nonadmission

FormProjectionProposition(CheckedEndpointSourceView, AdmittedOir, profile)
  -> FormedProjectionProposition

ValidateProjection(formed proposition, live authorities, checker, limits)
  -> Affirmative | Negative | qualified noncompletion
```

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

This schema is a joint PIR/OIR bridge contract. PIR owns extraction of that
graph. OIR owns independent construction, authentication, and local
interpretation. Neither owner can reinterpret one of its fields; an exact
schema or `DeriveEndpointContractV0` change rotates both the K3-D projection
profile and this OIR semantic profile. Sharing a value schema transfers no
source handle, read authority, or correctness.
Projection compares the independently formed canonical graph bodies exactly.

This is the minimum closed translation-validation boundary. It is stricter and
smaller than a general refinement relation, yet it preserves the decisive
separation between target validity and source correctness. A future optimizer,
rescheduler, split/fusion lowering, or ABI transformer must select a distinct
relation profile with exact rewrite laws and new falsification evidence. It
cannot weaken this profile in place.

## 3. Minimum semantic OIR

The complete bounded target identity is:

```text
OirEndpoint = {
  semantic_profile: OirSemanticProfileV0,
  semantic_graph: EndpointSemanticGraph
}
```

The exact graph schema is imported from
[PIR Endpoint Projection Views](../pir/endpoint-projection-views.md#appendix-a-exact-selected-source-view-body)
under the same exact K1 basis and semantic regime. It contains:

- role, exact-used dependencies, and exact value types;
- canonical constants and pure-node value graph;
- the slot-centric role ABI codec/slot/edge graph;
- exact total endpoint spine and K2 semantic frame coordinates;
- static Fiat--Shamir construction, prefix, namespace-recipe, retry, state,
  and failure laws;
- complete claim, reduction, publication, terminal, and closure graph;
- optional six-table reachable Plan graph.

The exact profile-owned `DeriveEndpointContractV0` evaluator derives one
closed `DerivedEndpointContractBody`: the complete static-obligation index,
the exact local-evaluator, counterparty, Plan-ingress, and storage
requirements, and the static completion interface. These are exact semantic
consequences, not second authored graph tables. Local admission reruns the
evaluator and validates the complete body; a producer cannot add, omit, or
override one row.

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
OirId =
  SemanticContentId<"oir.endpoint">(
    B, OirEndpointBody(endpoint))
```

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
semantics, not provenance. Interface codec/slot and Plan ordinals are local
graph refs and are rebased.

Consequently, two exact sources with the same complete endpoint quotient share
one semantic OIR. Dead Plan nodes, witness exports, and private source maps do
not rotate it. A reachable recipe, ABI edge, K2 framed coordinate, static FS
law, Check, Reduction, Terminal, or any graph operand from which a requirement
or completion-interface row is derived must rotate the OIR body or make reuse
projection-negative.

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
   Plan view read, but exclude private material, randomness, state, and Plan
   recipe intermediates;
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
   full terminal verdict, public outputs, required checks, and
   claim dispositions; then the finite K2 liveness, Last-Challenge,
   saturation, stopping, and linear-closure laws;
8. role shape and optional six-table Plan closure: FS is present for both
   supported roles; Verifier requires Plan absent; Prover requires Plan
   present; every Prover-message action has exactly one Plan move, every Plan
   decision key resolves to such an action, and decision-owned recipe nodes,
   exact
   coordinate/value decision reads, same-decision node references, randomness
   availability, total selected-state updates, recipe ABI, state, and
   action-spine cross-references;
9. one total rerun of `DeriveEndpointContractV0`, including the complete
   `DerivedEndpointContractBody`: every exact static obligation; local-only
   evaluator ownership and the exact graph-only `EndpointValueAccessV0`
   least-fixed-point route/operand check; locally demanded pure-node closure; General-codec
   presentation paths; counterparty contracts; private-material/randomness
   ingress; state storage; exact Verifier completion interface; no semantic
   Prover completion; and the four role/dataflow formation laws; and
10. cumulative K1 constitutional bounds for both the identity-bearing graph
    and the independently derived contract, plus explicit request-local work
    bounds; path-expansion oversize or exhaustion returns atomically with no
    partial contract.

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

## 6. Semantic proposition and validation request

The proposition states only semantic meaning:

```text
ProjectionProposition = {
  purpose: EndpointProjectionPurpose,
  source_view_id: EndpointSourceViewId,
  target_oir_id: OirId,
  relation_profile: K3DProjectionRelationV0
}
```

Procedure, authority, and audit data remain outside it:

```text
ProjectionValidationRequest = {
  proposition,
  exact admitted Protocol,
  exact admitted ProtocolInterface,
  optional exact admitted ProverPlan,
  optional exact affirmative CheckedPlanRealizes,
  exact affirmative SupportedExtractionBasis,
  exact affirmative CheckedEndpointSourceView,
  exact AdmittedOir,
  exact checker basis and evaluator,
  deterministic limits
}
```

Request formation reauthenticates every named body and requires the live
handles/capabilities to agree with the proposition IDs. Full source IDs,
manifest, realized reads, checker, limits, provenance, and evidence bind this
request and the resulting process-local capability, not proposition identity.
View-equivalent distinct sources may therefore share one proposition while
receiving distinct live capabilities.

There is no producer witness in this exact-equality profile. Removing it also
removes the earlier ambiguity between rejection of one witness and refutation
of an existential proposition.

## 7. Exact projection relation

Let `S` be the authenticated `EndpointSourceViewBody` retained by the checked
source capability, and `O` the independently admitted `OirEndpointBody`.
Bounded v0 defines:

```text
ProjectionCorrectV0(S,O) :=
  S.profile = K3DProjectionV0
  and O.profile = OirSemanticProfileV0
  and ContractLaw(S.profile) = EndpointContractLawV0
  and ContractLaw(O.profile) = EndpointContractLawV0
  and PurposeRole(S.purpose) = O.semantic_graph.role
  and M(S.semantic_graph) = M(O.semantic_graph)
```

The canonical encoder is injective, so byte equality here is exact typed graph
equality, not serialization coincidence. It covers every non-derived OIR
field at once: role, dependencies, types, constants, pure nodes, codec/slot
ABI, action spine/control order, static FS laws, claims, reduction/terminal
anchors, and optional Plan.

The equality compares original K2 transcript coordinates literally. It
compares local graph refs only after each side independently satisfies the one
canonical construction and ordering law. It does not compare source maps,
whole source IDs, read receipts, or runtime FS receipts. Positive graph
equality supplies exact no-omission and no-phantom coverage for every table.
Both profile formations also rerun the same exact
`DeriveEndpointContractV0`, so equality of the base graph entails equality of
the complete `DerivedEndpointContractBody`: static obligations, exact
requirements, and completion interface. No target universe can be silently
omitted from a correspondence witness because no such witness or partial
plane exists. The four role/dataflow laws in Section 3 are mandatory on both
formed graphs and need no second projection conjunct.

## 8. Outcomes and authority

The semantic Negative payload is closed and nonempty:

```text
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

Only Affirmative mints:

```text
ProjectedOirCapability<exact ProjectionValidationRequest>
```

The capability is opaque, linear where consumed, process-local, and bound to
the exact live source and target handles. Serialization transfers neither it
nor authority. Cold recovery reauthenticates and readmits every subject,
reclassifies support, re-extracts the source view, readmits OIR, reforms the
request, and reruns validation.

## 9. Role semantics and deferred endpoint pairing

For FS, both roles derive the same challenges locally from identical static
transcript semantics. A challenge is never ambient input. Every and only
Interface-declared `PublicDerivation -> ExternalApplication` export appears in
the Verifier ABI; cardinality is `0..n`. The Prover keeps the same derivation
internal.

The Verifier owns Checks, Reduction application, Terminal semantics, the
Protocol verdict, and every applicable completion presentation. The Prover
owns proof-message production and its reachable Plan but has
`NoSourceSemanticCompletion`. K2 `Stop`, unavailable authority, private search
exhaustion, and runtime FS exhaustion remain execution outcomes rather than
static completion claims.

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

| Source/purpose | `K3DProjectionV0` result |
|---|---|
| FS Verifier over base K2 non-Oracle, non-module effects | Supported |
| FS Plan-specialized Prover over base Plan recipes | Supported |
| Fresh Verifier or Prover | `Unsupported(FreshEndpoint)` |
| Generic Plan-free Prover | `Unsupported(GenericProverEndpoint)` |
| Core with a native Oracle declaration or occurrence | `Unsupported(StandardOracleEndpoint)` |
| Any admitted module effect | `Unsupported(ModuleEffectEndpoint)` |
| Future Interface/Plan grammar with module recipe | Fails the pinned regime/schema join; not classifiable under `K3DProjectionV0` |
| Legacy carrier lacking a supported K2 effect law | Stops at PIR admission |

The table is exhaustive for the closed purpose grammar and selected K2/K3-B
regime. A new source case or purpose rotates the profile and adds an explicit
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

Projection performs no arithmetization, polynomial-commitment selection,
batching, recursion, IOP compilation, or Fiat--Shamir conversion. Such a
transformation first needs its own admitted semantic target and checked
source/target relation.

## 12. Reopen rules and non-claims

No bounded K3-D pressure requires reopening K1, K2 Core/Fiat--Shamir, or K3-B
Interface/Plan identity. K3-D was reopened locally to retain K2 frame
coordinates, replace a static namespace datum with the per-draw recipe,
preserve the complete slot graph and claim/reduction/terminal structure, and
replace incomplete correspondence planes with total canonical equality.

Reopen this exact-equality profile only when a concrete supported endpoint
needs semantic reordering, optimization, split/fusion, ABI adaptation, or
another meaning-preserving nonidentity relation. Reopen K2 or K3-B only when a
positive endpoint inhabitant needs a source-owned fact their current exact
schemas cannot express.

The bounded executable instrument is a falsifier for this contract, not a
formal proof, complete OIR implementation, compiler-correctness theorem,
family-wide projectability result, or security claim.

## Appendix A. Exact OIR and projection bodies

All bodies use the exact K1 notation and the same `PriorMetaBasisId` and
selected `SemanticRegimeId` as the source graph. `CR(x)=Y(ContentRefV0(x))`.
`EndpointPurposeBody`, `K3DProjectionProfileBody`,
`EndpointContractLawV0Body`, `EndpointSemanticGraphBody`, and the complete
non-identity `DerivedEndpointContractBody` are imported exactly from the PIR
specification linked in Section 3; OIR cannot reinterpret their tags, fields,
local-reference rules, or bounds.

```text
OirSemanticProfileBody = R{
  0:V(0,U),1:EndpointContractLawV0Body
}
K3DProjectionRelationV0Body = V(0,U)

OirEndpointBody(x) = R{
  0:OirSemanticProfileBody,
  1:EndpointSemanticGraphBody(x.semantic_graph)
}

ProjectionPropositionBody(x) = R{
  0:EndpointPurposeBody(x.purpose),
  1:CR(x.source_view_id),
  2:CR(x.target_oir_id),
  3:K3DProjectionRelationV0Body
}
```

The semantic proposition has exactly four fields. Source IDs, manifest,
source maps, read receipts, support/extraction/admission capabilities, checker,
limits, evidence, and provenance are request inputs and cannot appear in this
body. K3-D defines no pair proposition body.

The OIR body must fit the cumulative K1 `2^20` encoded-byte, `2^14` node,
`2^14` aggregate-child-edge, and depth-384 limits. Local admission and
projection each also receive an explicit request-local work limit at most
`2^17`. Exhaustion is atomic and cannot be converted into Negative.
