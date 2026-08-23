# Stage 4B OIR-to-Realization entry contract

> **Document kind:** Temporary Stage 3.5 downstream handoff contract
> **Document state:** Bounded entry contract; no Stage 4B activation
> **Authority:** None. This page does not define or admit OIR, mint projection or
> realization authority, select a supplier, authorize deployment or invocation,
> or establish endpoint support.
> **Frozen basis:** The [Stage 3 target](target-semantic-model.md) at SHA-256
> `107255938efa6af7802030b93bdbc9dcb4d5535335866cffa304df33083a7f5b`
> and the [Stage 3 convergence record](convergence.md).
> **Successor owners:** [`oir/`](../../oir/README.md), followed by
> [`realization/`](../../realization/README.md).
> **Peer handoff:** [Stage 4A Analysis-to-Compiler entry
> contract](stage-4a-entry-contract.md).
> **Disposition:** Replace this page with reviewed durable OIR and Realization
> contracts after the entry obligations below are discharged.

## 1. Purpose and order

Stage 4B proceeds in this order:

```text
AdmittedProtocol
  + AdmittedProtocolInterface
  + EndpointRole
  + exact tagged ProjectionBasis
  + OIR regime and exact dependency closure
  -> unauthoritative OIR candidate
  -> independent OIR authentication and LocalOirValid admission
  -> exact source-relative ProjectionCorrect check

AdmittedOir
  + exact below-OIR inputs
  + TargetContract
  -> exact portable SupplierBinding
  -> separately admitted live provider authority
  -> effectful realization production
  -> target-specific RealizesOir check
  -> deployment, activation, invocation, and execution as separate lifecycles
```

OIR fixes endpoint meaning before Realization chooses an implementation.
Realization requirements may expose an omitted OIR observable and send a concrete
counterexample upstream, but supplier availability, backend convenience, or
deployment policy cannot change OIR behavior.

This page fixes only the downstream intake boundary. The separate activation
decision required by the [v0 design program](../../project/v0-design-program.md)
has not been made.

## 2. Frozen Stage 3 intake

Stage 4B consumes exact process-local authority reconstructed by Stage 3 owners.
The projection tuple is closed:

```text
ProjectionInput = {
  protocol: AdmittedProtocol[P],
  interface: AdmittedProtocolInterface[I -> P],
  role: EndpointRole,
  basis:
      InterfaceOnly
    | InterfaceAndPlan(
        plan: AdmittedPlan whose retained ProtocolId is P,
        plan_realizes: affirmative CheckedPlanRealizes
          over exactly protocol and plan),
  oir_regime: OirSemanticRegime,
  exact_dependency_closure,
  declared_source_read_set,
  source_view_adequacy
}
```

The exact Stage 3 source view contains only the events, ports and occurrences,
values and objects needed at the boundary, protected observations, challenges,
checks, claims, failures, terminals, endpoint obligations, prover obligations,
and interpretation facts declared by the projection question. It contains no
authoring provenance or composition history. It does not confer general
Protocol authority and cannot be replaced by canonical-PIR internals, carrier
labels, compiler state, cached projector state, a registry, or process defaults.

The closed entry tuple above contains no relation-correspondence or composition-
history premise. Projection under this tuple is therefore invariant under those
independently owned subjects. A later projection variant that genuinely reads
one must add the exact admitted operand and owner-checked capability as an
explicit tagged premise: `AdmittedRelationInterface` or an exact affirmative
`CheckedRelationCorrespondenceJudgment` whose retained Protocol and Interface
are exactly `protocol` and `interface` for relation-facing facts, and an
affirmative `CheckedCoreComposition` whose admitted target is `protocol` and
which retains `ResolvedCoreCompositionMaps` for composition history. It cannot
recover either from a Protocol view or provenance. For an FS
Protocol, interpretation facts are available only through the exact
`AdmittedProtocol` and its retained admitted `TranscriptConstruction`; a
construction ID or serialized map is insufficient.

`EndpointRole` is an explicit `RoleRef` restricted to exactly the unique Prover
or unique Verifier in the admitted Protocol. `PublicEnvironment` is not an
endpoint role. If projection consumes an Interface role entry, that entry must
map to this exact reference. The role is not inferred from a binary name,
command, deployment, or loaded backend.

## 3. Projection basis and Plan placement

The tagged basis has these exact meanings:

- verifier projection always uses `InterfaceOnly`, and its Plan read set is
  empty;
- a generic prover-obligation skeleton may use `InterfaceOnly` and therefore
  cannot read a Plan;
- a plan-specialized prover projection uses `InterfaceAndPlan` with the exact
  admitted Plan and affirmative exact `CheckedPlanRealizes`; and
- a negative, mismatched-question, mismatched-Protocol, serialized, or absent
  Plan-realization result cannot authorize the plan-specialized branch.

For every Plan field a prospective Stage 4B reader must compute and record one
of the Stage 3 semantic classes:

| Class | OIR rule | Realization rule |
|---|---|---|
| `ProjectionRelevant` | The field is read through `InterfaceAndPlan`; the full exact `ProverPlanId` enters the projection dependency and OIR identity | Realization preserves the already fixed OIR consequence and cannot reinterpret the field |
| `RealizationOnly` | The projector is forbidden to read it | It may enter through an explicit below-OIR Plan view and declared read set |
| `ExternalSupplyRequirement` | OIR must decide explicitly whether the requirement changes the endpoint input/requirement contract | If routed below OIR, Realization receives and binds it explicitly; the same fact cannot be read ambiently at both boundaries |

Classification is computed by the Stage 4B owner from exact OIR and Realization
semantics; a Plan field cannot self-assert its placement. Each projector and
realizer publishes its complete Plan field read set and an adequacy check. Plan
substitution that changes output without changing the declared basis is a
closure failure, not an optimization.

Plan admission supplies only well-formedness. `CheckedPlanRealizes` supplies
structural coverage, including occurrence-total private inputs, exact obligation
routes, basis/output maps, deadlines, and exact private-randomness ingress. It
does not supply witness values, providers, value correctness, stochastic
fidelity, termination, cost, or successful proof production.

## 4. OIR subject and local admission obligations

Before Stage 4B can produce an admitted OIR, the OIR owner must define a finite
closed contract for:

- verifier and prover endpoint kinds and role frames;
- the OIR grammar, canonical semantic encoding, carrier profile, `OirId`, typed
  local references, dependencies, authentication, and admission;
- endpoint ABI, public statement and context inputs, proof-stream behavior,
  witness and private-input capabilities, and result domains;
- protected transcript, challenge, check, claim, artifact, hole, failure,
  terminal, and completion effects;
- projected `check_call`, `hole_call`, resource, and abstract supplier-
  requirement semantics;
- abstract execution, ordering, refusal, malformed input, verifier
  accept/reject/abort, prover nonproduction, and other typed outcomes; and
- fail-closed extension and regime rules.

OIR authentication and local admission are OIR-owned operations over the exact
candidate, dependency preimages, authentication capabilities, law-checker
capabilities, and OIR regime. They must reconstruct identity and mint only an
opaque process-local `AdmittedOir` capability after `LocalOirValid` succeeds.

```text
LocalOirValid(O, OirSemanticRegime, exact_local_dependency_closure)
```

`LocalOirValid` may establish OIR grammar, identity, local typing, role frame,
ABI, local reference and linear-resource closure, and protected-effect well-
formedness. It has no admitted Protocol, Interface, role basis, or source
obligation set and therefore cannot establish origin, total source coverage, or
`ProjectionCorrect`.

## 5. Source-relative projection contract

Projection candidate production, OIR local admission, and source-relative
checking are three distinct transitions. The OIR owner must define closed
operations equivalent to:

```text
ProjectEndpoint(ProjectionInput)
  -> Qualified<CanonicalOirCandidate, ProjectionAudit>

AuthenticateAndAdmitOir(candidate, exact OIR dependencies and checkers)
  -> AdmittedOir

CheckProjection(ProjectionInput, AdmittedOir, exact projector/checker basis)
  -> Qualified<CheckedProjection>

CheckedProjection.payload =
    Affirmative(exact source/target maps and coverage facts)
  | Negative(nonempty typed mismatches, unaffected agreements)
```

The names and final carrier spelling are Stage 4B-owned; the separation and
inputs are mandatory. Candidate production grants no OIR admission or source
correspondence. Local admission grants no projection result. An affirmative
projection capability retains the exact Protocol, Interface, role, tagged basis,
OIR, regimes, source/target maps, read/dependency closure, checker identity, and
field-factored result. Only an affirmative exact `CheckedProjection` grants the
attenuated `ProjectedOirCapability` carrying `ProjectionCorrect`. The negative
variant retains no projected-OIR authority and cannot be cast to the
affirmative capability.

`ProjectionCorrect(P, I, role, basis, O)` must check at least:

- exact source identities, role, basis tag, and OIR regime;
- total coverage of every and only source endpoint obligations owned by that
  role, without using local OIR validity as a coverage witness;
- exact statement, context, proof-message, application, check, challenge,
  claim, failure, terminal, and result mappings selected by the Interface and
  role;
- preservation of schedule order, event-action occurrence, transcript-visible
  inputs/framing, protected observations, failure/abort/nonproduction
  distinctions, terminal payloads, and complete-consumption conditions;
- exact Plan read-set and obligation-route use for `InterfaceAndPlan`, and a
  proof of an empty Plan read set for `InterfaceOnly`;
- target local validity and identity under the exact admitted OIR; and
- closure of every dependency, source read, map, and abstract supplier
  requirement.

The Interface statement decoder supplies exactly one dependent
`ProtocolPublicAssignment<P>`: a total no-extra map over every and only public
input Statement occurrence of `P`. Proof positions denote the exact
`EventActionOccurs` predicate through the Interface's closed presence variants,
not a local activation guard, and realized positions preserve Core schedule
order. Pure Interface decoding returns only `Decoded` or exact `Malformed`; it
does not execute the Protocol or grant invocation authority. OIR may preserve
and expose these facts but cannot redefine their domains, presence, order, or
failure boundary.

Projection refusal, a completed negative projection result, malformed
input, missing source basis, missing authority, and checker failure remain
distinct. None invalidates the admitted Protocol or Interface.

## 6. Output exposure and availability

An Interface output port is only a typed grouping and lossless external
representation. It creates no Core occurrence, path-availability fact,
knowledge transfer, or OIR exposure.

Terminal outputs use the exact `InterfaceOutcome` mapping: every terminal has
one tag, and its payload is exactly the terminal's ordered public outputs. For
every other external output, `ProjectionCorrect` requires:

1. one exact OIR exposure occurrence owned by the projected endpoint role;
2. a source map to the exact Interface port/value grouping and Protocol value
   or object origins;
3. a visibility proof for the endpoint role;
4. a boundary- and path-indexed proof of
   `AvailableAt(role, source, source_boundary)` and the corresponding OIR-local
   availability at the exposure occurrence;
5. guard and multiplicity agreement, including selected-branch-only readiness
   for guarded merges; and
6. inclusion in the exact endpoint obligation/coverage account.

No projection may infer availability from declaration, output-port membership,
schedule position, public visibility alone, a carrier name, or successful local
OIR admission. If no legal occurrence and proof exist, projection refuses or
returns the exact negative result; Interface cannot repair the missing Core
fact, and Realization cannot create source-relative authority later.

## 7. OIR authority and persistence

OIR keeps these non-interchangeable local results and capabilities:

- `AdmittedOir`, establishing only `LocalOirValid`; and
- the exact A/N `CheckedProjection`; only its affirmative variant grants a
  `ProjectedOirCapability` establishing source-relative `ProjectionCorrect`
  while the admitted source tuple and OIR coexist.

Both are opaque and process-local. OIR serialization preserves canonical OIR
content, dependencies, and ordinary source references, never live admission or
projection authority. A cold consumer reauthenticates/readmits OIR and, if it
needs source coverage, reauthenticates every source and reruns the projection
check. A durable source-bound projection result requires a named independent
consumer and must bind the complete source tuple, basis, maps, regimes, checker,
qualified outcome, dependency/read closure, and residual trust.

## 8. Realization entry contract

Realization starts from endpoint meaning already fixed by an exact admitted OIR:

```text
AdmittedOir
  + optional BelowOirPlanBasis(
      source_link: affirmative ProjectedOirCapability
        retaining this exact AdmittedOir and the Protocol retained below,
      plan: AdmittedPlan,
      plan_realizes: affirmative CheckedPlanRealizes
        over exactly plan and its retained AdmittedProtocol,
      exact below-OIR field view and read set,
      placement: affirmative CheckedBelowOirPlanPlacement
        over exactly source_link, plan, plan_realizes, field view, read set,
        per-field classification, adequacy, placement regime, and checker)
  + TargetContract
  -> SupplierBinding
  -> AdmittedSupplierAuthority
  -> RealizationCandidate + EmissionObservation
  -> Qualified<RealizationCheckResult>
  -> AdmittedRealization only on the exact affirmative result
```

`CheckedBelowOirPlanPlacement` is a required future Stage 4B-owned pre-use
check, not a result minted by this page. Its affirmative variant establishes
that the source link, Plan-realization result, OIR, Plan, and retained Protocol
agree exactly; that every read field is `RealizationOnly` or an
`ExternalSupplyRequirement` explicitly routed below OIR; that no
`ProjectionRelevant` field is read; and that the declared view is adequate for
the complete read set. A completed negative retains only its exact mismatch
facts. U/C/R/M/F mint no placement capability.

The optional Plan basis therefore cannot reintroduce a `ProjectionRelevant`
choice, change OIR identity or behavior, or rely on an undeclared full-Plan
read. A standalone admitted OIR may still be realized without a Plan basis; a
Protocol-dependent Plan cannot be attached to it without the exact source link
and placement check above.

### 8.1 Supplier designation and live authority

```text
SupplierRequirementKey =
    OirRequirement(OirRequirementRef)
  | BelowOirPlanSupplyRequirement(
      ProverPlanId,
      SupplierRequirementRef)
```

`SupplierBinding` is a portable immutable configuration. Its key domain is
exactly every abstract OIR requirement plus, when `BelowOirPlanBasis` is
present, every and only Plan `ExternalSupplyRequirement` that the affirmative
placement result routes below OIR. The two tagged key families cannot alias. It
has exactly one compatible entry for every and only key in that union and binds
target, supplier, ABI, configuration, dependency, and provider-designation
identities. Unrelated catalog growth cannot change it.

The binding grants no access to a library, device, service, key, process, or
credential. A separate resolution and admission operation consumes an exact
provider snapshot, policy, regime, and live authentication capabilities and
mints narrow process-local `AdmittedSupplierAuthority`. Serialization preserves
the tagged binding data only, not the source link, Plan-placement capability, or
provider authority; effectful production must reconstruct all three when the
below-OIR Plan branch is present. Provider correctness, future availability,
performance, and semantic preservation remain unproved.

### 8.2 Effectful production and semantic checking

Realization production is effectful and separately attributed. It declares the
target, binding, live provider authority, resources, publication frontier,
retry/cleanup behavior, partial-production result, exact artifact identities,
and `EmissionObservation`. Producer success or equal bytes does not establish
`RealizesOir`.

The target-specific checker consumes the admitted OIR, exact target/binding,
candidate and artifacts, checker/model basis, regime, assumptions, and any named
trusted-producer boundary. It returns a qualified affirmative, fact-retaining
negative, unsupported, cannot-answer, refused, malformed, or checker-failure
outcome as applicable. Only the exact affirmative result can mint an admitted
realization capability. A trusted producer, when unavoidable, is an explicit
residual assumption and is never described as independent validation.

### 8.3 Deployment, activation, invocation, and execution

These transitions remain separate:

```text
AdmittedRealization + exact resource specification
  -> portable DeploymentBinding

DeploymentBinding + operator/resource authority
  -> activation occurrence + live revocable DeploymentCapability

SourceRelativeInvocation:
  DeploymentCapability for a realization of O
  + affirmative ProjectedOirCapability retaining P, I, role, and the same O
  + exact AdmittedProtocolInterface I
  + exact typed inputs already decoded under I
  + exact Interface algorithm execution capabilities
      iff this transition executes an Interface codec
  + caller authority + resources + invocation policy + invocation regime
  -> BoundInvocationCapability

StandaloneOirInvocation:
  DeploymentCapability for a realization of O
  + exact OIR-owned ABI inputs
  + caller authority + resources + invocation policy + invocation regime
  -> BoundInvocationCapability

BoundInvocationCapability + executor authority
  -> endpoint execution occurrence + typed result
     + attributed RawOperationalObservation
```

A deployment document is not live authority. Invocation reauthenticates every
join and attenuates authority by role, operation, lifetime, or use count. A
source-relative invocation cannot replace either the admitted Interface or the
affirmative source-to-OIR capability with an Interface ID, raw bytes, a local
OIR admission, or a deployment assertion. A standalone OIR invocation uses the
OIR-owned ABI and makes no Protocol-Interface or source-relative endpoint claim.
Execution creates a new occurrence even when content inputs are identical.
Verifier `Reject` is a completed endpoint result; malformed external input,
missing authority, provider refusal, executor failure, and residual partial
effects are distinct. Prover output means only that the exact occurrence
produced its declared bytes and observations.

Every effectful operation records resources touched, protected/completion
frontier, retry, cleanup or compensation, capability consumption on failure,
raw occurrence observation, and residual state. An observation remains
producer-owned material; Evidence appraisal and consumer reliance are later
owners.

## 9. Coordination with Stage 4A

The [Stage 4A entry contract](stage-4a-entry-contract.md) shares four boundaries
with this branch:

1. OIR and Analysis use the same Stage 3 observer, protected-observation,
   occurrence, transcript-order, failure, terminal, and nonproduction meanings.
2. `ProjectionCorrect`, `LocalOirValid`, and `RealizesOir` remain OIR/Realization
   results. An Analysis property may consume an exact result as a premise but
   cannot redefine or synthesize it from a property judgment.
3. OIR projection and Realization have no hidden dependency on Compiler
   selection. Any admitted Protocol may be projected, and any admitted OIR may
   be realized when its explicit inputs close. Compiler endpoint-feasibility
   constraints cite exact Stage 4B results rather than backend ambient state.
4. Plan reads are declared once at their owning boundary. Analysis questions,
   OIR projection, and Realization each cite the full exact subject and adequacy
   predicate when reading Plan fields; Realization additionally consumes the
   exact affirmative source link and below-OIR placement result; a Protocol-only
   claim must be invariant under Plan substitution.

Before either branch closes, both reconcile observer sets, protected effects,
Protocol/Interface/Plan identities, property-transport and projection
assumptions, verifier-visible order and transcript behavior, and every field one
branch treats as semantic while the other treats as configuration or runtime
state.

## 10. Prerequisites and entry gate

Research may use this contract as a boundary probe. Stage 4B must not be
activated until a separate decision confirms all of the following:

- the selected Stage 3 Protocol, canonical PIR, Interface, Plan, Relations,
  Fiat--Shamir, and composition contracts have been promoted into reviewed
  durable owners, with temporary-note absorption recorded;
- exact Protocol/Interface/Plan identities, authentication/admission,
  occurrence references, view attenuation, replay, qualified outcomes, and
  process-local capability rules consumed here are stable;
- the boundary-indexed `ExistsAt`, `KnowsAt`, and `AvailableAt` algebra, endpoint
  obligations, terminal payload rules, and Plan semantic-class constraints are
  available to the OIR owner through closed views;
- the initial OIR grammar, local dependency vocabulary, carrier/identity
  boundary, role and effect taxonomy, abstract execution result space, and
  exact projection question are enumerated rather than delegated to a backend;
- the initial target contract, tagged OIR/Plan supplier-requirement vocabulary,
  exact binding domain, binding and live-provider separation, realization-check
  basis, and partial-effect taxonomy are bounded;
- projector and realizer Plan read sets and adequacy checks are reconciled, the
  `CheckedBelowOirPlanPlacement` signature, qualified outcomes, source-link rule,
  and replay are closed, and verifier projection's empty read set is explicit;
  and
- the shared boundaries in Section 9 have been reconciled with the current
  Stage 4A entry contract.

An activation decision must name the bounded first endpoint roles and scenarios,
input views, owners, deliverables, verification plan, and exit gate. This page is
not that decision.

## 11. Required Stage 4B outputs

The branch is locally complete only when it produces reviewed owner documents
for:

- OIR grammar, carrier, identity, authentication/admission, ABI, protected
  effects, abstract execution, qualified outcomes, and extension rules;
- projection candidate production, exact source maps and coverage,
  `LocalOirValid`, `ProjectionCorrect`, Plan classification, nonterminal output
  exposure, replay, and persistence;
- below-OIR Plan placement, source-link authority, exact tagged supplier-
  requirement closure, target contracts, supplier bindings, live provider
  authority, effectful production, target-specific `RealizesOir`, admitted
  realization, and residual trust;
- deployment binding, activation, invocation, sessions, results, failure and
  partial-effect frontiers, observations, and capability lifetimes; and
- the cross-branch reconciliation record required by Section 9.

## 12. Exact nonclaims

This entry contract does not establish:

- OIR grammar validity, local admission, source-relative projection correctness,
  or endpoint support;
- output exposure or availability merely from an Interface output-port
  grouping, OIR declaration, source ID, or local OIR validity;
- Plan placement, realizability, completeness, prover success, termination,
  secrecy, performance, or cost;
- supplier correctness, live availability, artifact preservation, backend
  correctness, or `RealizesOir`;
- deployment readiness, activation success, invocation authority, runtime
  availability, endpoint acceptance, or absence of partial effects;
- a property theorem, Compiler feasibility/selection result, evidence appraisal,
  or consumer reliance; or
- Stage 4B activation, implementation authorization, migration, compatibility,
  or current backend support.
