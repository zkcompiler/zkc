# Compiler Core

Status: **normative v0.1 core semantics**. This document defines the in-memory
Compiler Core: general checked search over a shared, plan-driven Soundness
Kernel. Certificate packaging, artifact hardening, clean-room duplication, and
persisted request/result schemas are outside these compiler semantics;
persisted schemas may be added without changing the core judgments.

## 1. Compiler thesis

The compiler is **checked search over protocol-semantic transitions**:

```text
source protocol
  -> declared transform plan
  -> realized candidate protocol
  -> seal
  -> target-scoped conditional derivations
  -> legality and request constraints
  -> deterministic objective
  -> checked selection
```

Search is untrusted. The accepted result follows from deterministic core
judgments, not from optimizer annotations or claimed scores.

### 1.1 Protocol compilation and target realization

The **Protocol Compiler** operates on protocol-semantic objects and
transitions: seal authenticates the protocol spine, this Compiler Core searches
and checks protocol transformations, and endpoint projection derives
backend-neutral OIR. A prover OIR artifact records semantic dataflow as typed
handles, hole contracts, and construction routes; it does not select concrete
kernels, memory layouts, devices, or backend code.

A **Realization Compiler** is a distinct downstream layer. It consumes
authenticated OIR together with authenticated source/projection context and
resolves its abstract contracts to concrete implementations, layout and
scheduling decisions, target capabilities, and backend/provider calls. It then
emits an executable or realization plan plus the evidence needed to check that
resolution. It may optimize those choices but MUST NOT change the protocol
transcript, public ABI, claim graph, or hole contract meaning.

The `REALIZE` judgment in this document means realization of a candidate
**protocol-semantic transform plan**. It must not be confused with downstream
target realization.

Before generic target realization or multi-component witness plumbing can be
soundly designed, the boundary needs at least:

- relation payload/contract and relation-instance identity;
- an ordered public ABI bound to the exact statement instance;
- a witness-port schema and handle class bound to that relation instance and
  statement; and
- the exact hole or kernel contract the realization must implement.

Relation source compilation remains external to zkc. A versioned adapter may
interpret a relation compiler's output to validate its format and derive these
checked facts without moving relation compilation into the Protocol Compiler.

The compiler remains general in three ways:

1. domain providers discover source-dependent finite plan spaces;
2. transform families define reusable protocol-semantic transitions; and
3. objectives and constraints are request-defined within small closed
   grammars.

The `same_point_kzg_batch/v1` provider is one instance of this abstraction, not
its definition.

## 2. Boundary criteria

The compiler core contains a concept only when it changes:

- which plans are in the declared comparison scope;
- what protocol a plan realizes;
- whether the transition and resulting protocol are valid;
- which conditional derivations and losses constrain the candidate;
- what objective value the candidate has; or
- which eligible candidate is selected.

The following are not compiler-semantic concepts:

- complete canonical request/result/check byte equality;
- a separately governed checker artifact;
- registry-free bundling of every semantic preimage;
- canonical refusal diagnostics and stage logs;
- independent duplicate implementations of every provider and evaluator;
- release archives, manifests, provenance graphs, or reproduction records; and
- generic evidence, attestation, or policy services.

Those may be useful tooling or later assurance. They do not change the
research claim that a selection follows from a declared protocol-transform
space, conditional-security constraints, and deterministic objectives.

## 3. Core judgments

The stable compiler structure remains:

```text
DOMAIN -> REALIZE -> VALID -> SCORE -> SELECT -> DECIDE
```

### 3.1 `DOMAIN`

```text
DOMAIN(semantic_context, request) = canonical finite CompilerPlan set | refuse
```

The request names a transform-domain provider, a derivation-plan-domain
provider, requested targets, and finite bounds. The semantic context resolves
the exact provider and family definitions. The first provider derives
transform plans from authenticated source protocol structure. For each
realized transform plan, the second provider enumerates finite explicit
derivation-plan alternatives for the exact resolved targets. `DOMAIN` takes
their canonical finite product. Unsupported, unbounded, or incomplete domains
refuse.

Both `DOMAIN` and `REALIZE` reuse the same deterministic internal transform
operation:

```text
TRACE_REALIZE(semantic_context, request, transform_plan)
  = {sealed_final_artifact, checked_transform_trace} | refuse
```

It applies and checks transforms but performs no compiler-plan membership,
target derivation, constraint, score, or selection judgment. This avoids a
`DOMAIN`/`REALIZE` cycle without creating a second transformation semantics.

### 3.2 `REALIZE`

```text
REALIZE(semantic_context, request, submitted_plan_domain, ordinal)
  = Candidate | refuse
```

The public judgment recomputes `DOMAIN(semantic_context, request)`, requires
the submitted domain to match it exactly, and selects the plan at `ordinal`.
Every transform-plan application then matches exact source or intermediate
structure and executes one declared transform. The checked transform trace
resolves every stable request target to exact final-artifact claims, and every
resolved claim has one explicit derivation plan in canonical target order.
Subjects are recomputed from checked lineage rather than repeated inside the
plan. The final artifact, target resolution, and derivations are the result of
those checked inputs, not producer-supplied values merely associated with the
plan.

### 3.3 `VALID`

```text
VALID(semantic_context, request, submitted_plan_domain, ordinal)
  = ValidCandidate | refuse
```

Validity first performs the same exact-domain recomputation and then
recomputes the selected plan's realization and exact target derivations. It
checks transition legality, allowed primitive-game instances and qualitative
hypotheses, and exact loss ceilings. Provider enumeration or membership
belongs to the recomputed `DOMAIN`; objective inputs are consumed by `SCORE`.

### 3.4 `SCORE`

```text
SCORE(semantic_context, request, submitted_plan_domain, ordinal)
  = ScoredCandidate | refuse
```

`SCORE` revalidates the exact domain and `VALID` judgment before a
deterministic evaluator computes every term from checked candidate facts. The
admitted objective grammar includes exact static proof bytes.

### 3.5 `SELECT`

```text
SELECT(semantic_context, request, submitted_plan_domain)
  = selected ordinal | no_selection | refuse
```

`SELECT` recomputes the exact domain and independently validates and scores
every ordinal; producer-supplied candidate or score subsets are not inputs.
Selection follows the ordered objectives and uses the candidate's canonical
ordinal in the exact `PlanDomain` as the final tie-break.

### 3.6 `DECIDE`

```text
DECIDE(semantic_context, request, submitted_result) = accept | refuse
```

The decision checker reconstructs the declared plan scope and recomputes
realization, validity, scores, and selection. It does not trust
producer-authored candidate status, loss, cost, or selection.

## 4. Minimal semantic data

The v0 core uses in-memory request and result values. Persistence, canonical
encoding, migration, and result-inspection envelopes are intentionally
deferred. A checker verdict is a derived output, not a third semantic
authority.

### 4.1 `CompilerRequest`

```text
CompilerRequest {
  source_artifact
  comparison_scope:
    submitted_frontier | closed_domain
  exact_transform_domain_provider_ref
  exact_derivation_plan_domain_provider_ref
  submitted_compiler_plans    // required for submitted_frontier
  requested_targets: ordered [RequestedTarget]
  target_schemas
  allowed_binding/game/hypothesis surface
  soundness_constraints
  ordered_objectives
  finite_limits
}
```

Candidate artifact identities cannot appear in a shared request. A request
instead names a stable target key and a closed protocol-claim lineage
selector:

```text
TargetSchema {
  target_schema_key
  security_index
  resource_variable_declarations
}

RequestedTarget {
  target_key
  candidate_selector:
    ClaimLineage {
      ordered_source_claim_refs,
      select:
          FinalFrontier
        | TransformOutputs {
            transform_family_ref,
            exact_output_role
          }
    }
  admitted_target_schema_keys: nonempty ordered [target_schema_key]
}
```

`TargetSchema` values live once in the request-level `target_schemas` table;
each requested target names a nonempty, duplicate-free ordered subset by key.
Target schema keys are unique in that table. The source claim references are
exact, unique, and ordered. `FinalFrontier`
selects the surviving lineage after identities, renames, splits, and merges.
`TransformOutputs` selects only outputs with the exact role produced by the
named transform family along that lineage; it is empty when the candidate
does not apply that transform. This second form models introduced proof
obligations: the identity KZG candidate has no batch target, while a batching
candidate has one. Adding a selector that is not reducible to checked claim
correspondence is a specification change, not a provider callback.

The request contains the source artifact and binds exact provider and
representation references. `DECIDE` also receives an explicit immutable
`SemanticContext` resolving them to:

- exact `ArtifactSemantics` authorities;
- one native immutable `SoundnessContext`, including its closed catalog,
  selected binding refs, and resolved external parameters;
- transform-family definitions;
- transform-domain and derivation-plan-domain providers; and
- exact codec-width profiles required by the objective.

The `SoundnessContext` is constructed from a frozen signature at an ingress
boundary; that construction is not part of Compiler Core semantics. Artifact facts are
reconstructed only by the closed artifact-semantics projection and the
Soundness Kernel's finite projection vocabulary. The context cannot inject an
arbitrary fact resolver.

The context is an explicit function argument. v0 does not add a nominal
`soundness_context_ref`: such a reference would be meaningful only if derived
from the context's complete content. It need not be embedded as a
self-contained release bundle, and mutable ambient fallback is not allowed.

#### Artifact semantic authority

An input artifact is only an immutable representation payload plus the exact
`ArtifactSemantics` authority that interprets it. `AUTHENTICATE` reconstructs
the observations that the generic compiler may consume:

```text
AUTHENTICATE(exact_artifact_semantics, immutable_payload)
  = {artifact_id, sealed_soundness_view, ordered_verifier_proof_reads}
    | refuse
```

**The configured references.** An authority is named by an `ExactRef`
`(id, source_revision)`, and a configuration of them is named by a content
digest so that two runs are comparable exactly when they configured the same
authorities. The preimage is the canonical JSON object
`{"implementation": <ExactRef document>, "configuration": <the configured
document>}`, hashed under one of three domain tags —
`"zkc/compiler/pir-artifact-semantics-config\n"`,
`"zkc/compiler/transform-family-config\n"`,
`"zkc/compiler/transform-domain-config\n"` — and reported in `sha256:<hex>`
form. An `ExactRef` document is `{"id": <string>, "source_revision":
<string>}`. This is stated here because the cross-implementation gate compares
these digests, and a digest whose preimage lives only in two implementations
is agreement rather than conformance.

There are no producer-populated mirrors of the soundness view, artifact id, or
proof-read list. The result is an immutable authenticated-artifact handle used
by domain, transform, derivation, and objective judgments. Each raw successor
is authenticated before its family checker consumes it or it becomes the next
predecessor. This is the one representation-neutral authority boundary: the
generic core neither imports PIR nor defines a second sealing algorithm.
Repeated anti-forgery mirrors and deep comparison are artifact hardening and
remain post-v0.

### 4.2 `TransformPlan`

```text
TransformPlan {
  ordered applications [
    transform_family
    match_anchor
    parameters
  ]
}
```

The empty plan is identity. Plans may contain multiple applications. Order is
semantic because later matches resolve against the preceding intermediate
artifact.

The transform plan has canonical semantic content but is only one component of
the compiler plan.

Every checked application emits one or more exact claim correspondences:

```text
ClaimCorrespondence {
  application_index
  transform_family_ref
  ordered_consumed_claim_refs
  ordered_produced_claims [
    {claim_ref, output_role}
  ]
}
```

They are derived by the transform-family checker from the actual stage-local
before/after artifacts. References in one correspondence are interpreted only
at that application index. They are not optimizer annotations and do not
assert an application-level relation.

`TARGET_RESOLVE` carries an ordered lineage frontier. Each element contains
one current claim ref, its nonempty ordered source-root ordinals, and an
ordered set of provenance tags `(application_index, transform_family_ref,
output_role)`. Starting from the requested source claims:

1. when a correspondence does not intersect the frontier, it leaves it
   unchanged;
2. otherwise, its consumed refs must occur exactly once as a subsequence of
   the frontier and in the correspondence's stated order, and every consumed
   ref must belong to that frontier;
3. the resolver removes those elements and inserts the produced claims at the
   first consumed position, in produced order; all unaffected elements retain
   relative order;
4. each produced element inherits the stable ordered union of the consumed
   source-root ordinals and provenance tags, then appends its own exact
   production tag; and
5. duplicate produced refs, a partial merge with an untracked claim, an empty
   consumed or produced sequence, or any stage-local reference mismatch
   refuses.

Thus provenance propagates through later rename, split, and merge operations.
`FinalFrontier` selects the final ordered frontier.
`TransformOutputs(family, role)` selects, in final-frontier order, each unique
final descendant whose inherited provenance contains a matching family/role
tag. A final claim is returned once even if several matching ancestors merge
into it; split descendants remain separate. This is the only source used by
`TransformOutputs`, so an intermediate raw claim ref never masquerades as a
final target.

```text
TARGET_RESOLVE(source, checked_transform_trace, final_artifact,
               RequestedTarget)
  = ordered [SecuritySubject::ProtocolClaim] | refuse
```

`FinalFrontier` must return a nonempty sequence. `TransformOutputs` may return
an empty sequence and otherwise uses the deterministic final-frontier order.
`TARGET_RESOLVE` returns exact subjects, not caller-selected theorem
coordinates: each result is
`ProtocolClaim(final_artifact.artifact_id, resolved_claim_ref)`. The
`CompilerTargetPlan` selects one admitted target schema and combines that
subject with the schema's index and resource declarations to form the exact
`DerivationTarget`. The empty transform plan therefore resolves to the exact
source frontier; a merge may resolve several source claims to one final claim,
while an introduced-output selector resolves to no target for identity.

### 4.3 `CompilerPlan`

```text
CompilerTargetPlan {
  target_key
  target_schema_key: admitted key | NoneWhenEmpty
  derivation_plans: ordered [DerivationPlan]
}

CompilerPlan {
  transform_plan: TransformPlan
  target_plans: ordered [CompilerTargetPlan]
}
```

Every request target key occurs exactly once, in canonical request order, and
no extra key occurs. Within each entry, derivation plans occur in
`TARGET_RESOLVE` order. The checker recomputes the subjects and combines them
with the named schema's index/resources; the plan does not duplicate those
derived subjects. All nonempty members under one key therefore have a
homogeneous index and resource schema; a heterogeneous split uses separate
requested target keys. An empty resolution must use `NoneWhenEmpty`, so unused
schema alternatives do not create distinct plans. A derivation plan is
semantic input because several valid paths may reach the same exact target
with different bounds or hypotheses. The derivation-plan-domain provider may
enumerate finite alternatives, but the compiler never reconstructs a path by
ambient search.

```text
PlanIdentity = CompilerPlan
```

Plan equality is exact structural equality. Enumeration order is semantic and
provides the final deterministic ordinal tie-break; v0 does not add a
cryptographic request or plan digest.

### 4.4 `Candidate`

```text
Candidate {
  domain_ordinal
  compiler_plan
  checked_transform_trace
  target_derivations
}
```

`Candidate` is an evaluator result, not a producer report. `VALID` wraps it
only after the derivation surface and soundness constraints hold. `SCORE`
reads objective inputs directly from the final authenticated artifact; it
does not repeat the same proof-read vector once per objective.

`DerivationResult` is deterministic from the final artifact, target,
soundness context, and the exact derivation plan already included in
the compiler plan; it need not be folded into identity a second time.

### 4.5 `CompilerResult`

```text
CompilerResult {
  selected_domain_ordinal | no_selection
}
```

`DECIDE` already receives the request and semantic context and recomputes
`DOMAIN`, so repeating the request reference, comparison scope, and every
considered plan would add an inspection envelope rather than semantics.
Acceptance requires only that the recomputed selected ordinal agrees.

The checker may emit:

```text
DecisionVerdict {
  accepted | refused {reason}
}
```

This is a derived in-memory view. A richer report, content-addressed
`CompilerCheckV1`, or complete result-byte equality is future additive work.

## 5. Domain providers and transform families

### 5.1 Finite domain providers

Transform-space enumeration and derivation-plan enumeration are separate:

```text
TransformDomainProvider:
  exact_ref
  artifact_semantics_ref
  enumerate_transforms(request, source)
    -> finite canonical TransformPlan set
  transform_member(request, source, transform_plan)
    -> yes | no

DerivationPlanDomainProvider:
  enumerate_plans(request, sealed_candidate, requested_target,
                  target_schema, resolved_subject)
    -> finite canonical DerivationPlan set
  plan_member(request, sealed_candidate, requested_target,
              target_schema, resolved_subject, derivation_plan)
    -> yes | no
```

For `closed_domain`, `DOMAIN` enumerates transform plans, runs
`TRACE_REALIZE`, resolves the requested targets, enumerates a finite plan set
for every admitted homogeneous target-schema choice and each resolved subject,
and takes the canonical product. For
`submitted_frontier`, it runs both membership predicates after recomputing
the same transform trace and target resolution.
An empty resolution contributes exactly the singleton `NoneWhenEmpty` target
entry and invokes no derivation-plan provider.

This separation keeps theorem search outside `SoundnessKernel` without making
each transform provider responsible for an unspecified proof search.
Derivation-plan enumeration may use the selected or request-allowed exact
binding references plus closed external assumptions, but it must return a
finite explicit set under the request bounds. Each binding determines its
executable rule; there is no second rule allowlist. An empty set makes that
transform plan contribute no
`CompilerPlan`; an unsupported or unbounded enumeration refuses the whole
closed domain rather than silently pruning it.
Likewise, an enumerated transform plan that cannot pass `TRACE_REALIZE`
refuses the declared closed domain; a provider cannot obtain a smaller domain
by emitting unrealizable plans and dropping them afterward.

Provider bounds include only what is required to make the domains finite, such
as maximum groups, applications, derivation depth, and listed binding,
parameter, and external-assumption alternatives. Changing bounds
changes the declared comparison domain. A provider cannot silently prune
plans according to runtime policy, expected cost, or optimizer preference;
those belong to validity or selection.

The decision checker reruns the normative provider functions independently of
the producer's search result. These semantics do not require a second provider
implementation; the provider definitions remain part of the trusted surface.

### 5.2 Transform family

A transform family defines:

```text
exact_ref
artifact_semantics_ref
recognize(artifact, match_anchor, parameters)
  -> unique canonical match | refuse
realize(artifact, canonical_match, parameters)
  -> unique canonical next artifact | refuse
check(before, after, match, parameters)
  -> checked [ClaimCorrespondence] | refuse
```

Every semantic choice affecting output must be explicit in the plan's match
anchor or parameters. `realize` is a deterministic normative function:
identical inputs produce one exact next artifact under the protocol's
structural equality. `TRACE_REALIZE` uses it and then requires `check` to
accept that exact before/after pair.
The transform-domain provider, every selected transform family, the source,
and each successor must name the same exact `ArtifactSemantics` authority.
An unknown or mismatched authority refuses before the artifact can enter a
checked trace.
Untrusted search may use its own convenience recognizer or builder, but
producer output is never the input from which `DECIDE` chooses an artifact.

`check` establishes that:

- the match exists at the exact named coordinates;
- the parameters are in the request's finite domain;
- consumed and produced protocol claims are correct;
- the emitted claim correspondences exactly describe those consumed and
  produced claims;
- transcript and material structure changes match the family semantics;
- every introduced protocol and reduction anchor is exact; and
- the next intermediate artifact is exactly the transform result.

Binding and derivation-path correspondence is checked later by `DOMAIN`'s
derivation-plan enumeration or membership and `REALIZE`'s `DERIVE` judgment
against the exact resolved target. It is not an input to structural transform
checking.

A transform family is protocol-semantic. It does not claim backend
code-generation or prover equivalence.

### 5.3 Multi-application plans

For:

```text
P0 --a1--> P1 --a2--> ... --an--> Pn
```

every application is checked against its actual predecessor. The final
checked transform trace is the legality judgment: there is no second
request-selected legality profile. A family may enforce additional local
conditions inside `recognize` or `check` when its semantics require them.

The compiler cannot validate only `P0` and `Pn` while trusting producer-authored
intermediate matches.

## 6. Candidate realization

`REALIZE` performs:

```text
authenticate source
  -> select the exact CompilerPlan at its PlanDomain ordinal
  -> TRACE_REALIZE using the shared transform semantics,
     authenticating every successor before check/use
  -> retain the authenticated final successor
  -> resolve every requested lineage frontier
  -> derive every resolved target through its exact target plan
  -> retain the fully checked transform trace and derivations
```

The public `REALIZE` entrypoint recomputes and exactly compares `DOMAIN`, so a
caller cannot substitute or mutate a plan domain. After that check, the
canonical realization path does not repeat provider enumeration, evaluate
soundness constraints, or score objective inputs. `DOMAIN` owns the provider
enumeration/membership judgment, `VALID` owns derivation-surface and bound
constraints, and `SCORE` reads objective inputs from the authenticated final
artifact.

An identity transform plan must reproduce the source artifact under the
declared realization semantics. Its `CompilerPlan` still carries an explicit
derivation plan for every claim in each resolved target frontier; identity
receives no special soundness or objective value by convention.

The compiler may orchestrate existing tools. The semantic authority remains
the judgments, not a particular pipeline process layout or pass manifest.

## 7. Validity and soundness constraints

`VALID` is:

```text
PlanMember
AND RealizeOK
AND FinalArtifactAuthenticationOK
AND RequestedDerivationsOK
AND CheckedTransformTraceOK
AND RuleAndConditionConstraintsOK
AND LossCeilingsOK
```

### 7.1 Soundness integration

For every resolved target in every requested target frontier:

```text
DERIVE(soundness_context, final_artifact, target, target_plan)
  = DerivationResult
```

The compiler consumes the representation-neutral `DERIVE` result. It does not
implement a compiler-local pricing model. `target_plan` is read from the
`CompilerPlan`, and `DECIDE` reruns that exact plan.

The request may constrain:

- allowed binding refs;
- allowed exact primitive-game instances;
- allowed exact external proposition instances;
- requested target keys, resolved subjects, indices, result schemas, resource
  schemas, and derived regimes; and
- exact loss ceilings.

These are local compilation constraints, not a general runtime policy or
evidence language. `AssumedJudgmentHolds` is not caller-authorized here:
`DERIVE` creates that marker only for an explicit marker-free `Assume` leaf,
and `VALID` accepts it only while walking the exact evaluated tree rooted at
that leaf. Allowing an external proposition does not prove it, and allowing a
primitive-game instance does not numerically bound its advantage.

### 7.2 `LEGAL`

For v0, `LEGAL` is the checked transform trace itself. Every application runs
the exact family's `recognize -> realize -> check` sequence against its actual
authenticated predecessor and successor. The family checker owns the
protocol-semantic transition relation; the compiler validates its exact
application-indexed claim correspondence and composes the checked steps.

There is no separately selected legality profile and no generic policy grammar
for allowances. A versioned relation-payload adapter may add authenticated
interface facts at the compiler boundary without changing the compiler's
search, lineage, derivation, or selection judgments; it does not make the
external relation language a kernel-owned semantics.

`LEGAL` establishes the structural transition and, with §7.3, the bound
relation. It establishes nothing else. Completeness, zero knowledge, witness
indistinguishability, and every other property of the protocol are outside it:
a legal transform is one that preserves the transition and does not degrade the
bound, and a family that also preserves some other property does so by an
argument this judgment never reads. A consumer that needs such a property must
obtain it elsewhere and may not infer it from acceptance here.

A family that does preserve one says so, and saying so is not the same as
establishing it:

```text
PreservationClaim {
  property_ref,        // an open identifier
  family_ref,          // exact, revision included
  application_index
}
```

`property_ref` is open, and that is the point rather than an omission. Which
properties can be claimed, and what a claim about one is conditional on, are
decided by the programs that take those properties on. Completeness is a
separate conditional track in the Soundness Kernel; zero knowledge requires
its own semantics and mechanization; and a
preservation claim is only as strong as the consumer that checks it. Settling
their vocabulary from `LEGAL` would make this judgment decide their scope,
which is exactly the inference §7.2 refuses. What is fixed here is only that a
family has somewhere to put a claim, and that the record says who made it.

Claiming nothing is the default. A claim is collected after the family's
`check` and is never consulted by it, so it cannot make an illegal transform
legal and cannot make a legal one more so; the one thing `realizeTransform`
requires of a claim is that it name a property, and that it name its own author
and application: attributing one elsewhere would put a family on the hook for
an argument it never made. The checked trace carries the claims in application
order.

The point is where the argument is, not whether it exists. A consumer holding a
claim has been told whose argument to go and read; a consumer holding none has
been told that nobody has offered one. Both are better than the silence that
made the property folklore.

A derivation witness carries the claims that reached its artifact in a
`preservation_obligations` section, beside the conclusion rather than inside
it: what a transform claimed to preserve is not what the derivation
established, and the two have different authors. A checker repeats them and
does not re-derive them, because it holds the artifact and the signature and
not the trace that produced the artifact.

### 7.3 Exact conditional-loss ceilings

Bounds are read only from checked `DerivationResult`s. There is no v0
artifact-global security sum and not every `SecurityResult` has a bound
coordinate.

```text
BoundProjection :=
    ExtractionFailure
  | Round(exact_round_index)
  | RoundMaximum
  | Scalar
```

The projection is typed:

- `ExtractionFailure` requires computational special soundness;
- `Round` and `RoundMaximum` require RBR; and
- `Scalar` requires SR or FS.

Projecting an information-theoretic special-soundness result or a mismatched
coordinate refuses.

Every constraint declares one comparison domain:

```text
ComparisonDomain {
  resource_variable_declarations
}
```

A target read first projects a checked result and then applies a total,
type-preserving substitution from that result's resources into the comparison
domain. Candidate and baseline expressions use one algebra:

```text
BoundExpr :=
    Zero
  | CandidateTargetRead {
      target_key,
      members: ExactOrdinal(nonnegative_integer) | Fold(Add | Max),
      projection: BoundProjection,
      resource_substitutions:
        map<target_schema_key, total resource substitution>
    }
  | SourceProjection {
      source_target: DerivationTarget,
      source_derivation_plan: DerivationPlan,
      projection: BoundProjection,
      resource_substitution,
      target_relation:
        SourceMemberOf {
          target_key,
          exact_source_claim_ref
        }
    }
  | Add([BoundExpr])
  | Max([BoundExpr])
  | Scale(nonnegative ClosedQuantity, BoundExpr)

SoundnessConstraint {
  comparison_domain,
  candidate: BoundExpr,
  baseline: BoundExpr,
  ceiling: ClosedBound over comparison_domain
}
```

The grammar is mode-checked: a candidate admits `CandidateTargetRead`,
`Add`, `Max`, and `Scale`; a baseline admits `Zero`, `SourceProjection`,
`Add`, `Max`, and `Scale`. A candidate fold reads every resolved target in
`TARGET_RESOLVE` order. For an introduced-output target, `Fold(Add)` of an
empty resolution is exactly zero; `Fold(Max)` of an empty resolution refuses.
Each candidate read selects the substitution keyed by its
`CompilerTargetPlan.target_schema_key`. The map must cover every admitted
nonempty schema reachable for that request target, and each substitution must
be total from that schema into the constraint comparison domain.

There is one relational meaning:

```text
BOUND_LEQ(candidate_bound, baseline_bound + ceiling)
```

A total ceiling is the same relation with `baseline = Zero`. A nonzero source
baseline is an introduced-loss envelope, not a sum of “local contributions”
and not symbolic subtraction.

Every source projection is recomputed by four-argument `DERIVE` against the
sealed source artifact. Its exact subject must be
`ProtocolClaim(source.artifact_id, exact_source_claim_ref)`, and
`SourceMemberOf` must resolve in the named `RequestedTarget`'s source
frontier. The candidate expression must contain a leaf or fold with that same
`target_key`, and the checked transform trace must place the source member in
the preimage of a final claim read by that same-key candidate node. Cross-key
baselines are not admitted in v0; they require a future explicit checked
relation. These checks are the source-to-candidate relation, so an unrelated
source bound cannot be used as a baseline.

Every baseline derivation is subject to the request's same allowed binding,
primitive-game-instance, and qualitative-hypothesis constraints as a candidate
derivation. The binding already determines the executable rule; there is no
second rule allowlist. Using a conditional source judgment in an inequality
does not discharge or hide its hypotheses.

The source resource substitution is total and maps the whole projected source
judgment view into the constraint's comparison domain before the projection is
normalized. Candidate reads are specialized in the same way. `Zero` is
explicit and makes the constraint equivalent to a total ceiling. `Add`,
`Max`, and `Scale` are request-declared envelopes; the compiler does not claim
that they are a canonical decomposition of transformation loss.

Candidate, baseline, and ceiling are compared in the declared resource domain.
Their primitive-game support need not be equal: a game key absent from one
side has coefficient zero. This permits an introduced transform to add a
primitive-game term while keeping comparison exact. An undeclared resource,
an ill-typed or partial substitution, a source projection outside the checked
lineage preimage, or a bound that cannot close in the common domain refuses.
The construction remains meaningful through `Scale`, `Max`, claim merges, and
result-shape transforms without inventing additive provenance.

`BOUND_LEQ` is a partial exact checker over the Soundness Kernel's v0 normal
form. It normalizes ground rational terms, non-negative resource monomials,
and exact primitive-game instances, then requires coefficient-wise domination
at identical keys. A ground `Max` normalizes to its exact maximum; unsupported
symbolic maxima or incomparable resource/game coordinates refuse. No symbolic
advantage becomes a numeric bit estimate without an explicit future game-bound
rule.

## 8. Objective model

```text
ObjectiveTerm {
  evaluator
  direction: minimize | maximize
}
```

The request orders terms lexicographically. The candidate's canonical ordinal
in the exact `PlanDomain` is the final tie-break. The ordinal reflects the
declared provider enumeration/product order; no second structural plan key is
constructed.

The v0 evaluator is:

```text
static_proof_bytes(
  authenticated_final_artifact.verifier_proof_reads,
  exact_codec_width_profile_ref
)
```

It reads the authenticated final artifact's ordered verifier-proof reads and
resolves each exact codec ref in the named width profile, then sums:

```text
checked multiplicity * exact width
```

with arbitrary-precision exact rational arithmetic. Request validation
requires every codec width to be a positive integer, so no machine-integer
overflow case is part of this judgment.

It does not estimate or claim:

- prover time;
- verifier time;
- memory;
- proof material absent from the authenticated read list;
- backend execution; or
- wall-clock performance.

Future measured objectives require explicit measurement semantics and inputs.
They do not require changing the six compiler judgments.

## 9. Selection and comparison scope

Candidates with failed validity or unavailable objective terms are ineligible.

```text
eligible =
  all CompilerPlans in exact scope
  whose REALIZE, VALID, and SCORE judgments succeed

selected =
  lexicographic best eligible candidate
  with canonical PlanDomain ordinal as final tie-break
```

If no candidate is eligible, the result is `no_selection`.

For `submitted_frontier`:

- the exact submitted `CompilerPlan` set is request data;
- every compiler plan must satisfy provider `member`; and
- the claim is best among that exact set.

For `closed_domain`:

- the checker runs provider `enumerate`;
- the finite result is the exact internal comparison domain; and
- the claim is best among all eligible plans in that provider-defined domain.

The core does not call `member` again on values just returned by
`enumerate`; that would be provider self-consistency hardening. `member`
remains required for a caller-supplied `submitted_frontier`.

Neither scope implies global optimality outside the exact request.

## 10. Decision checking

`DECIDE` performs the following semantic work:

1. resolve and authenticate the request's exact source and semantic context;
2. establish the exact `CompilerPlan` set for the declared comparison scope;
3. realize every compiler plan in scope, authenticating every successor before
   its transition checker may consume it;
4. run required target derivations over each final authenticated artifact;
5. check transform correspondence, `LEGAL`, allowed primitive-game instances,
   qualitative hypotheses, and loss ceilings;
6. recompute objective values;
7. recompute eligibility and selection; and
8. compare the submitted selected ordinal with the recomputed decision.

The checker may share:

- parsers and canonical encoders;
- Protocol Kernel and `SoundnessKernel`;
- domain-provider and transform-family semantic implementations;
- transform-family checks and artifact projection;
- objective evaluators; and
- primitive exact arithmetic.

What it must not trust is producer output: enumerated compiler plans, match success,
candidate validity, loss, score, eligibility, or selection.

This is a checked compiler boundary. It is not a claim of implementation
independence or common-mode-bug elimination.

## 11. Same-point KZG provider

The provider is `same_point_kzg_batch/v1`.

### 11.1 Source-derived domain

The provider discovers maximal disjoint groups of compatible
`single_opening` claims sharing the exact point anchor and satisfying the
batch transform's structural preconditions.

The provider definition pins one positive `batch_space`. Its
exact reference commits both the artifact-semantics identity and this value.
For multiple disjoint groups, it builds canonical batching combinations under
the request's finite application bound; the identity plan is the empty
combination.

Domain inclusion is not candidate validity. A compiler plan may be in
`DOMAIN` and later fail a premise, allowed-game/hypothesis constraint, loss,
legality, or objective constraint.

The batching transform accepts an exact group selector and structural
parameters only. It selects no theorem. After the resulting batch
claim is resolved, the derivation-plan provider enumerates request-listed
binding alternatives whose subject and target schemas match that exact claim.
Each binding fixes its executable rule. This separation produces one
structural transform paired with each valid theorem path, rather than
cross-producting two independently authored choices. A pass that rewrites
every group or selects a rule from ambient state cannot faithfully
realize the provider domain.

## 12. Authority composition

The physical library, file, and tool split is not normative. Semantic
authority is divided as follows:

- Protocol Kernel owns seal;
- `SoundnessKernel` owns theorem application and conditional loss;
- transform families own local before/after semantics;
- the compiler composes those authorities into candidate evaluation and
  selection; and
- `DECIDE` recomputes the semantic decision from explicit inputs.

An independent implementation may provide additional assurance, but it is not
part of these core semantics.

## 13. Explicit exclusions

The compiler core excludes:

- source-language relation compilation and circuit-compiler correctness;
- general relation-payload decoding or refinement;
- subject-bound witness schemas, witness generation, and witness lifting;
- a general Realization Compiler, prover/backend code generation, layout and
  scheduling selection, and backend equivalence;
- generic evidence, attestation, or policy frameworks;
- formal-proof consumption during compilation;
- source-supply-chain and release-manifest ontologies;
- clean-room duplicate evaluator requirements;
- distributed search, auto-tuning services, or benchmark databases;
- a general optimizer DSL before another provider requires one; and
- claims about theorem truth, proof acceptance, or backend execution.
