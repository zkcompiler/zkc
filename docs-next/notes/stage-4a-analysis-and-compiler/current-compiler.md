# Current Compiler reconstruction

> **Document kind:** Temporary Stage 4A current-model reconstruction
> **Document state:** Complete for Stage 4A.1; target-neutral
> **Authority:** None. Current normative meaning remains in
> [`docs/spec/compiler.md`](../../../docs/spec/compiler.md). Code, tests, and
> status pages are correspondence evidence only. This page does not repair a
> disagreement, select a target, establish compiler correctness, or authorize
> implementation or migration.
> **Reconstructed:** 2026-08-22
> **Disposition:** Retain current strengths, conflicts, and unknowns in the
> Stage 4A gap record; delete this page with the temporary package after
> reviewed conclusions have durable owners.

## 1. Reading result

The current Compiler is an in-memory deterministic checked-search engine over
one exact finite set of Protocol-transform and Soundness-derivation plans:

```text
DOMAIN -> REALIZE -> VALID -> SCORE -> SELECT -> DECIDE
```

It is unusually disciplined about immutable artifact authority, exact provider
configuration, checked claim lineage, finite comparison scope, exact bound
arithmetic, and recomputation of a submitted decision. Its central Stage 4A
limitation is not an absence of checks. It is that proposal production, target
admission, family-local transform checking, Soundness derivation, eligibility,
and selection remain assembled inside one Soundness-specific request, while
the public result retains only an optional domain ordinal.

The normative Compiler is not the later Realization Compiler. Current
`REALIZE` constructs a Protocol-semantic candidate; later target realization
implements fixed OIR. The specification distinguishes the two meanings, but
the shared term remains an architectural collision.

## 2. Authority map

| Surface | Current role | What it cannot establish |
|---|---|---|
| `docs/spec/compiler.md` | Normative current Compiler semantics | Implementation correspondence or target Stage 4A design |
| `docs/spec/soundness.md` | Normative shared derivation and bound semantics consumed by Compiler | General Analysis, theorem truth, or an independently admitted Compiler input |
| `docs/status.md` | Implemented and exercised scope | Semantics, generality, or future work |
| `docs/roadmap.md` | Work order | Current support or semantic authority |
| `docs/architecture.md` | Explanatory system placement | A conflicting normative rule |
| `include/zkc/Compiler/`, `lib/Compiler/` | Implementation correspondence and feasibility evidence | Intended meaning where it conflicts with a specification |
| `test/Compiler/`, `test/lib/TestCompilerCore.cpp`, `TestPirCompilerProvider.cpp` | Bounded behavior and refusal evidence | General correctness, completeness, or independent checking |
| `reference/oracle/compiler.py` | Independent configuration-digest twin | Compiler decision parity or conformance to the normative preimage |

The current specification and the frozen Stage 3 handoff describe different
architectural moments. Neither may be silently read as an erratum for the
other.

## 3. Current semantic context and ingress

The generic core is representation-neutral. A producer supplies:

```text
OwnedCompilerArtifact {
  exact ArtifactSemantics reference,
  immutable typed payload
}
```

`ArtifactSemantics::authenticateArtifact` applies the exact authority to the
payload, reconstructs rather than trusts artifact identity, the owned
`SealedSoundnessView`, and ordered verifier proof reads, then mints an
immutable authenticated compiler artifact. Transform and derivation providers
consume that capability, not producer-populated observation mirrors.

The exact `SemanticContext` closes:

- representation-specific artifact semantics;
- one immutable Soundness context and catalog;
- transform-family definitions;
- transform-domain and derivation-plan-domain providers; and
- exact codec-width profiles used by objectives.

The PIR adapter retains an already admitted PIR capability and the complete
`ProtocolEnvironment` required by the current compiler configuration. Provider
configuration identity deliberately includes the complete normalized
vocabulary and configured profiles rather than only the Protocol's consumed
identity closure. This makes compiler configurations comparable without
changing Protocol identity.

## 4. Request and plan model

The current request contains:

```text
CompilerRequest {
  source_artifact,
  comparison_scope,
  exact transform-domain provider,
  exact derivation-domain provider,
  submitted plans when required,
  requested target lineages,
  target schemas,
  allowed binding/game/hypothesis surface,
  Soundness constraints,
  ordered objectives,
  finite limits
}
```

Candidate artifact identities cannot occur in the request because candidates
do not exist yet. A requested target instead identifies source claim roots and
one lineage selector:

- final surviving frontier; or
- final descendants carrying an exact transform-family/output-role tag.

One `CompilerPlan` combines an ordered `TransformPlan` with one exact
derivation-plan choice for every resolved target subject. Plan equality is
exact structural equality. There is no normative request, domain, plan, or
candidate digest.

This plan has two different semantic choices:

1. which Protocol transformations to request; and
2. which explicit Soundness derivation to check for each resulting subject.

The second choice is why two plans may realize the same transformed artifact
yet remain distinct members of the comparison domain.

## 5. Judgment reconstruction

### 5.1 `DOMAIN`

`DOMAIN` validates the request and constructs one canonical finite
`CompilerPlan` set.

For `closed_domain`, it:

1. enumerates transform plans;
2. fully executes, seals, authenticates, and checks each transform plan;
3. resolves exact final subjects through checked lineage;
4. enumerates finite derivation alternatives for every subject/schema choice;
5. takes the bounded canonical product; and
6. refuses duplicates, overflow, unsupportedness, or provider failure.

For `submitted_frontier`, the caller supplies the exact plan set and both
providers check membership after the same target and transform reconstruction.

The domain is therefore not a syntactic declaration. Closed-domain
construction already performs expensive semantic work. A transform or
authentication operational failure may refuse the whole domain, while absence
of a derivation alternative removes the corresponding product member.

The two comparison claims remain bounded:

- `closed_domain` means best in the exact provider-enumerated domain; and
- `submitted_frontier` means best in the exact submitted member-checked set.

Neither is global optimality.

### 5.2 `REALIZE`

Every public stage recomputes `DOMAIN` and requires exact equality with the
submitted plan domain. `REALIZE` then selects an ordinal and:

1. replays each transform application against its immediate predecessor;
2. authenticates each raw successor before its family checker or next step
   consumes it;
3. retains the checked correspondence trace;
4. resolves target lineages against the final artifact; and
5. runs the shared Soundness `DERIVE` evaluator for the selected explicit
   derivation plan of every target.

The resulting `Candidate` is an evaluator product, not a producer report.

### 5.3 `VALID`

`VALID` re-runs realization and checks:

- authenticated final-artifact and transform-trace conditions;
- allowed rule bindings, exact primitive-game instances, and external
  propositions;
- canonical `AssumedJudgmentHolds` provenance;
- typed candidate/source bound projections and total substitutions; and
- exact `candidate <= baseline + ceiling` constraints.

The bound algebra supports scalar, extraction-failure, exact-round, and
round-maximum projections together with exact `Add`, ground `Max`, and
nonnegative `Scale`. A source baseline must reach the candidate through the
same checked claim lineage; an unrelated or cross-target source result cannot
price a candidate.

This is strong exact arithmetic over current Soundness results. It is not a
general constraint algebra over independently admitted Analysis judgments.

### 5.4 `SCORE`

The sole implemented objective is exact static verifier proof bytes:

```text
sum(authenticated proof-read multiplicity * exact codec byte width)
```

The objective does not estimate prover time, verifier time, memory, backend
execution, endpoint feasibility, or wall-clock performance. Missing objective
data makes that candidate ineligible.

### 5.5 `SELECT`

`SELECT` evaluates every domain ordinal. Candidate-local derivation, bound, or
objective failure becomes internal ineligibility; an authentication, provider,
malformed-state, or operational checker failure aborts the compilation.

Eligible candidates are compared lexicographically. The domain ordinal is the
final tie-break. Consequently provider or submitted-frontier ordering is
semantic even when two candidates have equal objective values.

If no candidate is eligible, the current result is successful
`no_selection`. The public surface does not expose why each candidate was
ineligible or distinguish all Stage 3 qualified outcome classes.

### 5.6 `DECIDE`

The public result is only:

```text
CompilerResult { selected_domain_ordinal | no_selection }
```

`DECIDE` receives the same request and context, recomputes the entire
compilation, and compares the optional ordinal. It correctly distrusts
producer-authored plan, candidate, validity, score, eligibility, and selection
claims. It does not yield a persistent selected target, candidate assessment,
checked edge, score vector, or decision replay package.

## 6. Transform-family and relation meaning

A current transform family defines:

```text
recognize(predecessor, anchor, parameters)
  -> canonical application | refuse

realize(predecessor, canonical application)
  -> unique successor | refuse

check(predecessor, successor, canonical application)
  -> checked claim correspondences | refuse
```

The normative function `realize` makes the family's output deterministic.
Generic transform execution authenticates the successor before invoking
`check` and validates every correspondence.

`ClaimCorrespondence` is a lineage fact, not an application-level semantic
relation. It records exact consumed and produced claims and propagates source
roots and production tags through rename, split, merge, and survivor steps.
It does not establish Protocol equality, trace refinement, distributional
preservation, or a property theorem.

Current `LEGAL` is the checked family trace. It establishes the family-defined
structural transition and, together with explicit constraints, the current
bound relation. There is no first-class qualified predecessor/successor
relation subject or capability independent of the compiler pipeline.

### 6.1 Same-point KZG provider

The one substantive provider discovers pairwise-disjoint maximal same-point
KZG groups. It enumerates identity followed by bounded group combinations in
increasing application count and lexicographic discovered-group order.

For each KZG application, the current provider's `realize` operation itself:

```text
reopens admitted predecessor
  -> mutates Open PIR
  -> seals
  -> snapshots/decodes
  -> admits successor
  -> wraps the admitted payload
```

The later family `check` independently reopens the predecessor, repeats the
transformation, reseals, compares target identity, and derives claim
correspondences. This is a useful replay check, but proposal construction and
PIR target admission are fused inside the provider. The frozen Stage 3 target
instead requires an unauthoritative proposal followed by PIR-owned
authentication/admission and only then a separately qualified exact relation
check.

Survivor correspondence pairs equal descriptor-digest groups in canonical
claim order after the exact replay has established target identity. Present
fixtures cover this rule; its general adequacy for unrelated future transform
families is unestablished.

## 7. Analysis coupling

The current Compiler directly owns or embeds:

- `SoundnessContext`;
- derivation-domain enumeration and membership;
- allowed binding, primitive-game, and hypothesis surfaces;
- exact Soundness bound projection and arithmetic; and
- re-execution of `DERIVE` for every candidate target.

There is no independent admitted Analysis result or question-scoped live
capability consumed by Compiler. The current sharing is still valuable: every
consumer uses the one Soundness evaluator and cannot invent a second pricing
semantics. Stage 4A must preserve that single-meaning property while moving
question, basis, derivation, and result authority to Analysis rather than
duplicating the calculus inside Compiler.

## 8. Preservation claims

`PreservationClaim` is an attributed open string naming a property, family,
and application. It is collected after the family's checked transition and is
never consulted by legality. Tests deliberately show that adding or removing
such a claim changes the record but not the legal verdict.

It is therefore an offered obligation or pointer to an author's argument, not
a checked property result. It cannot become an affirmative Compiler constraint
without a separate Analysis-owned property-transport judgment. This current
non-implication is correct and must be retained.

## 9. Identity, replay, and persistence

Three different current mechanisms must not be collapsed:

1. PIR artifacts can be persisted, decoded, and re-admitted.
2. The KZG transform can be replayed by the same family implementation and its
   exact successor identity checked.
3. A Compiler decision can be freshly recomputed only when the same in-memory request,
   semantic context, provider behavior, and domain order are supplied.

There is no normative persistent Compiler request, domain, plan, proposal,
candidate, checked edge, assessment, decision, or replay schema. The selected
ordinal is not meaningful independently of the exact domain.

`DECIDE` reuses the same configured artifact semantics, providers, transform
families, Soundness evaluator, objective semantics, and arithmetic. It
distrusts submitted producer results but does not provide implementation-
independent checking or common-mode assurance. `CompilerResult` and
`DecisionVerdict` are public owned values rather than opaque live
capabilities.

No production Compiler command is installed. Current Compiler passes are test
surfaces, and current status describes an in-process checked-search core with
one bounded provider.

## 10. Exercised correspondence

The focused live Compiler suite passed four of four tests. Its covered cases
include:

- canonical closed domains and submitted frontiers;
- exact derivation alternatives and shared Soundness evaluation;
- candidate-local ineligibility versus fatal operational failure;
- exact bound substitutions and source/candidate lineage;
- introduced, split, merged, and surviving claims;
- deterministic ties, no selection, and decision recomputation;
- one- and two-group same-point KZG batching; and
- configured-authority and cycle refusals.

The representative single-group provider domain contains identity plus two
derivation alternatives for the batched target. Static proof-byte scores are
`96`, `48`, and `48`; one transformed alternative is ineligible under its
bound ceiling, and ordinal `1` is selected. These are bounded fixture results,
not evidence of general domain completeness or Compiler correctness.

## 11. Normative and implementation conflict

The current Compiler specification says an exact configuration reference is
encoded as the JSON object:

```json
{"id": "...", "source_revision": "..."}
```

The C++ implementation and independent Python configuration twin encode it as
a two-element array:

```json
["...", "..."]
```

They also use the implemented KZG-specific family/domain tags. The parity test
therefore establishes C++/Python agreement, not conformance to the normative
preimage. This is a real current conflict and remains unresolved by this
reconstruction.

## 12. Current strengths to preserve

1. Producer search and claimed scores are not decision authority.
2. Every semantic input is exact and immutable at the generic core boundary.
3. Each successor is authenticated before later semantic consumption.
4. Multi-step lineage is checked against actual intermediate predecessors.
5. Domain and objective scopes are finite, declared, and deterministic.
6. Bound arithmetic is exact and refuses unsupported comparisons.
7. Soundness derivation has one shared meaning rather than a compiler-local
   approximation.
8. `no_selection` is a bounded result rather than a fabricated candidate.
9. Selection proves nothing outside the declared comparison scope.
10. Unchecked preservation attribution is not property truth.

## 13. Current-to-frozen seam map

| Current model | Frozen Stage 3 pressure | Classification |
|---|---|---|
| Provider `realize` constructs and admits the target | Proposal must be unauthoritative; PIR independently authenticates and admits | Split |
| Family trace plus claim correspondence is `LEGAL` | Exact predecessor/successor relation has a named question, qualified result, and capability | Replace/complete |
| Compiler embeds Soundness context, plans, and bound grammar | Compiler consumes exact qualified Analysis results | Split |
| `PreservationClaim` is an open unchecked attribution | Property transport is an Analysis-owned exact judgment | Retain nonclaim; replace as eligibility input |
| Closed provider enumeration and submitted frontier | Domain scope and completeness meaning must be explicit | Retain and generalize |
| Ordinal is final tie-break and public decision | Stable candidate/decision identity and explicit total tie rule remain open | Reconsider |
| Candidate-ineligible versus generic operational error | Full qualified outcomes and negative facts are required | Expand |
| Freshly recompute entire provider pipeline under the same configured authorities | Independent-consumer cold replay and optional consumer-justified persistence | Redesign |
| Static proof-byte objective | Typed exact property and cost inputs may be consumed | Generalize without implicit backend coupling |

## 14. Open questions preserved for redesign

- What exact object defines a candidate comparison domain independently of
  mutable provider state?
- When is a domain complete by explicit enumeration, by checked symbolic
  description, or only relative to a submitted frontier?
- May an incomplete exploratory search yield a useful choice without claiming
  an optimum or `NoSelection`?
- Should equal-score ties use provider order, stable candidate identity, or an
  explicit request objective?
- When two plans produce the same admitted Protocol under different checked
  edges or Analysis bases, are they one target or different assessed
  candidates?
- Which transform families admit a materially smaller direct checker, which
  need theorem/certificate validation, and which remain honestly trusted?
- Which failures make one candidate ineligible, which leave a successful
  negative fact, and which make the whole decision incomplete?
- What exact selected result must a Compiler consumer receive besides an
  ordinal?
- Which named consumer, if any, justifies a persistent decision record rather
  than direct bounded recomputation?
- How can expensive checked work be memoized without turning cache records into
  semantic authority?
- How does endpoint feasibility enter only through an exact Stage 4B-owned
  result rather than hidden provider state?

## 15. Reconstruction conclusion

The current Compiler supplies a strong checked-search control: it does not
trust optimizer reports, authenticates every intermediate successor, computes
exact conditional constraints, and bounds every selection claim. Stage 4A
must not discard those strengths.

The target question is nevertheless broader than alignment. An ideal Compiler
must make producer proposal, PIR admission, exact transform relation, Analysis
property transport, candidate assessment, objective observation, domain
closure, selection, replay, and trust independently visible. Only then can
heuristic producers, proof-producing checkers, equality-saturation engines,
or future endpoint constraints compete without inheriting semantic authority
from the current same-point KZG provider shape.
