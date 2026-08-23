# Realization and runtime

> **Document kind:** Domain index
> **Document state:** Scaffold
> **Target alignment:** Stage 3 input boundary closed; Stage 4B not activated
> **Provisional owner:** `realization`
> **Authority:** None during the transition. Current realization material is
> split among the reserved [boundary contract](../../docs/spec/boundaries.md),
> the non-normative [target architecture](../../docs/architecture.md), and
> operational claims in [Current Status](../../docs/status.md).

## Purpose

`realization/` owns the downstream lifecycle that implements a fixed admitted
OIR endpoint: exact supplier binding, effectful artifact production,
target-specific preservation checking, deployment preparation and activation,
invocation binding and execution, and producer-owned operational
observations.

This domain preserves a semantic firewall: OIR fixes accepted endpoint
behavior; realization chooses and operates an implementation without acquiring
authority to change that behavior.

## Owns

- target contracts, realization requests, and concrete capability
  descriptions;
- exact supplier bindings for codecs, sponges, checks, holes, kernels,
  services, or other abstract OIR requirements;
- the distinction between portable supplier designation and live resolved
  provider authority;
- concrete CheckContract and HoleContract supplier selection and execution;
- effectful realization production, generated artifacts, content identity,
  provenance, and partial-production outcomes;
- target-specific `RealizesOir` checking and admitted realization capability;
- lowering, scheduling, fast-path, and backend preservation contracts;
- portable deployment bindings, activation occurrences, resource bindings,
  and live deployment capabilities;
- invocation binding, per-run attenuated authority, sessions, and concrete
  endpoint execution;
- typed verifier/prover results, refusals, operational failures, and
  partial-effect failures; and
- attributed emission, activation, invocation, run, and session observations
  before Evidence records them.

Much of this surface is not yet normative. Architecture-only and reserved
topics remain labeled as such until their exact schemas, relations, and
identities exist.

## Does not own

- relation, Protocol, Interface, Plan, or OIR meaning;
- Protocol transformations or accepted-behavior changes;
- endpoint projection, canonical OIR identity, or `ProjectionCorrect`;
- property, security, completeness, or zero-knowledge conclusions;
- the evidence interpretation granted to an operational observation;
- appraisal policy or a consumer's use-specific reliance decision; or
- current public support claims.

A realizer may optimize while preserving OIR. If it changes transcript
behavior, proof ABI, public binding, checks, artifacts, claims, protected
events, or terminal decisions, it is no longer merely realization and must
return to the owning semantic layer.

## Selected lifecycle boundaries

The downstream path is a sequence of distinct contracts, not one lowering
arrow:

```text
AdmittedOir
  + optional BelowOirPlanBasis(
      source_link: affirmative ProjectedOirCapability retaining this exact OIR
        and its Protocol/Interface/role basis,
      plan: AdmittedPlan,
      plan_realizes: affirmative CheckedPlanRealizes over exactly that Protocol
        and Plan,
      exact below-OIR field view and read set,
      placement: affirmative CheckedBelowOirPlanPlacement over the exact source
        link, Plan, Plan-realization result, field classification, adequacy,
        regime, and checker)
  + TargetContract
  -> exact SupplierBinding configuration
  -> AdmittedSupplierAuthority
  -> effectful RealizationCandidate production + EmissionObservation
  -> Qualified<RealizationCheckResult>
  -> AdmittedRealization only on the exact affirmative result
  -> portable DeploymentBinding
  -> activation occurrence + live DeploymentCapability
  -> BoundInvocationCapability
  -> endpoint execution + typed result + RawOperationalObservation
```

Product commands may combine adjacent operations, but their results must say
which gates completed, which capabilities were created or consumed, and which
external effects remain.

### Supplier binding

Supplier binding is an exact closed designation, not ambient matching or
negotiation. Every abstract OIR requirement has exactly one compatible binding
entry, superfluous entries are rejected, and unrelated catalog growth cannot
change the result. A below-OIR `ProverPlan` is an explicit tagged input only
when binding or realization reads it. It must arrive through the complete
`BelowOirPlanBasis`: the affirmative exact source-to-OIR capability, exact
admitted Plan and affirmative `CheckedPlanRealizes`, complete field view and
read set, and affirmative `CheckedBelowOirPlanPlacement`. Plan admission or
`CheckedPlanRealizes` alone is insufficient, and a standalone OIR cannot acquire
a Protocol-dependent Plan without that exact source-relative join.

The binding key domain is a tagged disjoint union of every and only abstract OIR
requirement and, when the below-OIR branch is present, every and only Plan
`ExternalSupplyRequirement` that the affirmative placement result routes below
OIR. `OirRequirement` and `BelowOirPlanSupplyRequirement(ProverPlanId, ...)`
cannot alias. A `ProjectionRelevant` field cannot enter this union or be reread
below OIR.

The portable `SupplierBinding` identifies configuration and provider
designations. It does not grant access to libraries, devices, services, keys,
or processes. A separate process-local admitted supplier authority retains
narrow live provider authority. Serialization preserves only the tagged binding
data, never the source link, Plan-placement capability, or provider authority. A
receiver must reconstruct the complete below-OIR basis when present and
re-resolve and re-admit provider authority.

Binding establishes exact requirement closure and ABI compatibility. It does
not establish provider correctness, availability at a later activation,
protected-behavior preservation, performance, or endpoint acceptance.

### Production and realization checking

Producing bytes and establishing semantic preservation are separate logical
transitions:

```text
ProduceRealization(...) -> RealizationCandidate + EmissionObservation

CheckRealization(
  AdmittedOir,
  exact target and binding,
  candidate and artifacts,
  checker/model basis,
  regime,
  assumptions,
  optional named trusted-producer boundary) ->
  Qualified<RealizationCheckResult>

RealizationCheckResult =
    Affirmative(exact RealizesOir facts)
  | Negative(nonempty typed mismatches or counterexample facts)
  | Unsupported(exact unsupported target or check)
  | CannotAnswer(missing named semantic basis)
  | Refused(missing authority or prohibited invocation)
  | Malformed(exact framing or structural defect)
  | CheckerFailure(operational failure with no semantic conclusion)
```

An implementation may initially trust one emitter when no smaller checker is
practical, but it must name that trusted boundary. Producer success, a
matching manifest, a successful build, or conformance tests do not by
themselves establish `RealizesOir`. Only the exact affirmative result can mint
`AdmittedRealization`; a completed negative retains only its exact mismatch or
counterexample facts. Production refusal, missing basis or authority, malformed
input, checker failure, operational failure, and partial-effect failure remain
different outcomes.

The assurance path is target-specific. A target-specific validator, such as
translation validation, or an exact checker/model basis that cites a separately
verified producer theorem and its correspondence may establish `RealizesOir`.
When neither is practical, the target-specific check may return an affirmative
result only under an explicitly named trusted-producer boundary retained as a
residual assumption, without pretending that independent validation occurred.
A consumer-justified portable witness may carry only its exact qualified result
after the persistence gate passes; it never serializes a live capability.
Bounded conformance Evidence and interpreter observations do not themselves
establish `RealizesOir`.

### Deployment and invocation

Deployment preparation forms a portable realization-to-resource plan and
checks that its role and resource designations are permitted by the admitted
realization. It grants no live operator or resource authority. Activation is a
separate effectful occurrence that consumes those authorities and creates a
scoped, revocable live capability. A serialized deployment document is never
live deployment authority.

Invocation has two explicit variants. A source-relative invocation
reauthenticates the join among the deployment capability, the affirmative
`ProjectedOirCapability` retaining the same OIR/Protocol/Interface/role, the
exact admitted Interface, typed inputs decoded under it, any exact Interface
algorithm execution capabilities actually invoked, caller/resource authority,
policy, and regime. A standalone OIR invocation instead consumes the exact
OIR-owned ABI inputs and makes no Protocol-Interface or source-relative claim.
Neither path may reconstruct the missing join from IDs, raw bytes, local OIR
admission, deployment assertions, or provenance. A bound capability may
attenuate broad authority to one port, operation set, lifetime, or use count.
Execution then creates a new occurrence. Verifier `Reject` is a completed
semantic endpoint result; malformed external input, missing authority,
supplier refusal, executor failure, and residual partial effects are separate
categories. Prover success states only that one occurrence produced bytes and
declared observables.

## Identity, capability, and effect rules

Immutable content/configuration identities and operational occurrence
identities remain distinct:

```text
OirId
SupplierBindingId
ArtifactContentId
RealizationId
DeploymentBindingId

EmissionOccurrenceId
DeploymentInstanceId
InvocationId / RunId
```

Equal artifact bytes do not collapse two production occurrences. Equal
deployment configuration does not identify two live instances. Repeating an
invocation creates a new occurrence even if every content input is equal.

Every effectful producer specifies its publication, activation,
protected-event, or completion frontier as applicable, together with resources
touched, retry behavior, cleanup or compensation, raw occurrence observation,
and residual state after failure. Invocation in particular declares the last
protected event completed before an operational or partial-effect failure. A
partial-effect failure cannot be reported as a pure refusal. Copying,
borrowing, revocation, expiry, concurrency, and consumption-on-failure are
defined separately for supplier, deployment, and invocation capabilities; no
generic handle supplies those semantics.

## Dependencies

- `foundation/` for identity, authentication, admission, encoding, capability,
  and lifecycle mechanisms;
- `oir/` for admitted endpoint semantics, ABI, abstract requirements,
  protected effects, and preservation obligations;
- the PIR `ProverPlan` owner only through a complete `BelowOirPlanBasis` carrying
  the exact affirmative source link, admitted Plan, affirmative
  `CheckedPlanRealizes`, declared view/read set, and affirmative
  `CheckedBelowOirPlanPlacement`;
- `relations/` only for an explicitly declared relation-facing realization or
  invocation variant that adds its exact admitted operands, owner-checked
  capability, and complete read set; and
- external provider designation identities pinned by portable bindings, with
  live provider authority accepted only by the separate resolution/admission,
  production, activation, or invocation operation that names it.

Realization does not semantically depend on compiler selection. Any admitted
endpoint may be realized if a target and exact suppliers can satisfy its
contract.

## Consumers and outputs

- operators deploy and invoke admitted realizations through scoped
  capabilities;
- `evidence/` may record exact artifacts, environments, observations, and run
  results without reinterpreting their producer-owned meaning;
- `project/` summarizes supported realization paths through global status; and
- guides describe emission, deployment, and invocation workflows.

## Bridge ownership

`realization/` owns these distinct transitions:

1. admitted OIR and optional complete `BelowOirPlanBasis` containing the exact
   affirmative source link, admitted Plan, affirmative `CheckedPlanRealizes`,
   field view/read set, and affirmative `CheckedBelowOirPlanPlacement` to exact
   tagged supplier binding;
2. exact binding plus provider resolver snapshot, admission policy, and regime
   to narrow process-local live provider authority;
3. OIR plus exact binding, reconstructed complete below-OIR basis when present,
   and admitted live provider authority to an effectfully produced candidate;
4. admitted OIR, exact target and binding, candidate and artifacts, checker/
   model basis, regime, assumptions, and any named trusted-producer boundary to
   the full qualified realization result; only its affirmative variant mints
   `AdmittedRealization`;
5. admitted realization plus resource specification to deployment binding;
6. admitted deployment binding plus operator authority to activation and a
   live capability;
7. either the exact source-relative join of live deployment, affirmative
   `ProjectedOirCapability`, admitted Interface, decoded inputs and any invoked
   Interface algorithm authority, or the standalone join of live deployment
   and exact OIR-owned ABI inputs, plus caller/resource authority, policy, and
   regime, to a bound invocation; and
8. bound invocation plus executor authority to an endpoint result and
   attributed observation.

Each transition states its own identities, dependency closure, authority
effect, refusals, residual assumptions, and partial-effect frontier. The
observation-to-Evidence-record bridge belongs to `evidence/`; the producing
operation retains authority over what its observation means, and the relying
consumer owns any decision to act.

## Candidate internal topics

- targets, providers, exact supplier bindings, and provider capabilities;
- emission, generated artifacts, and realization checking;
- lowering, scheduling, and fast paths;
- deployment configuration, activation, and resource lifecycle;
- invocation binding, sessions, and runtime capabilities; and
- concrete execution, result production, and operational observations.

## Open design questions

- What exact abstract-requirement, target-contract, binding, provider, and
  capability schemas realize the selected supplier boundary?
- Which `ProverPlan` fields remain explicit below OIR, and at which earliest
  transition is each consumed?
- What target-specific facets and trusted assumptions define `RealizesOir`,
  and which backends have a genuinely smaller independent checker?
- What artifact/package identity, atomic-publication, retry, and
  partial-production contracts are required per target?
- What deployment topology, mutable-resource, activation, revocation, and
  cleanup schemas are required?
- What invocation/session APIs, exact role-specific results, concurrency,
  retry, sensitivity, and partial-effect rules are required?
- Should deployment and invocation become separate subdomains once their
  subjects and lifecycles support several durable pages?
