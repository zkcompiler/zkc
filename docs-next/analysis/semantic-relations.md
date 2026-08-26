# Analysis semantic relation families

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative target
> **Target status:** Stage 4A durable promotion
> **Provisional owner:** `analysis`
> **Authority:** This document specifies the selected target for `docs-next/`.
> It is non-normative until explicit consolidation and cutover. The current
> specifications under [`docs/`](../../docs/README.md) remain authoritative.
> This document establishes no relation, property, cost, implementation, or
> migration result.

> **K1 transition notice — 2026-08-26:** The identity, canonical-value,
> algorithm, dependency, and checked-result forms below predate
> [Executable Semantic Foundations](../foundation/executable-foundations.md).
> K3 must reconcile these Analysis families with the exact K1 substrate and
> the K2 Protocol model; this page is not yet a K1-integrated calculus.

## 1. Scope and common contract

This document defines the direct Analysis families for:

- Core and Protocol equality under an exact map;
- observable trace equality and directed trace refinement;
- conformance to an admitted declaration of intentional change;
- distribution equality and directional closeness; and
- exact or qualified cost values and relations.

It also fixes the ownership seam to `RelationSatisfies`, which belongs to
Relations rather than Analysis.

All families use the lifecycle, identity, hypothesis, basis, qualification,
negative-result, and capability rules in the
[Analysis semantic model](analysis-model.md). The admitted Protocol and Core
meanings come from the [Protocol semantic model](../pir/protocol-model.md).
Relation operands and structural correspondence come from the
[Relation semantic model](../relations/relation-model.md) and
[Protocol correspondence](../relations/protocol-correspondence.md).

Every operation below executes through the complete occurrence-local
`AnalysisCheckingInvocation`: exact authenticated request and family policy,
all typed admitted-subject/view and checked-result source bindings, the total
source-policy closure, separately supplied fresh source and checker
capabilities, and the exact named consumer and typed purpose. Signatures may
elide this envelope for readability; no operation may read an ambient value,
policy, binding, or authority.

Every question closes:

~~~text
exact admitted subject tuple
exact family semantic profile and model
exact observer, direction, occurrences, and total maps
complete semantic read closure through owner-created views
typed parameters and quantifiers
exact conclusion and residual hypothesis context
~~~

A source ID match, relation adjacency, proposal annotation, shared bytes, or
producer report cannot establish any family result. A successful check mints
only the exact family-, proposition-, polarity-, assurance-, scope-, and
`FamilyOperationPolicyId`-indexed process-local capability retaining its exact
judgment-record/basis/derivation/support/validation binding and complete
transitive source-operation-policy dependency closure, plus its complete
`ExactCheckedResultAuthorityBinding<Analysis,F>` and inert
`OwnerCapabilityRequirement`.

## 2. Map and comparison discipline

### 2.1 Exact typed maps

Every comparison map is a separately authenticated finite typed value. It
names the exact source and target subject IDs and regimes, its direction, each
mapped kind, every occurrence in its domain, and its totality and uniqueness
policy. Kinds never alias merely because ordinals or encodings coincide.

A family profile states which maps are semantic inputs and which equations
they must preserve. A map can cover exactly the domain declared by one
question without being a universal Protocol isomorphism. A checker cannot
repair a missing entry, infer an ambient correspondence, or choose a more
favorable map after observing the comparison result.

An incomplete, ill-typed, non-total, duplicated, wrong-kind, or operand-
mismatched map proposal is malformed and establishes no comparison result.
This is distinct from a well-formed map that fails one exact preservation
equation.

### 2.2 Exact under-map versus existential claims

The v0 direct families primarily check one supplied exact map. A negative
under that map refutes only that exact under-map proposition. It does not
refute the existence of another valid map.

Existential isomorphism, refinement under some map, or best-map search is a
different family with a separately declared finite search domain and complete
decision or refutation boundary. Failure to discover a map is
`CannotAnswer`, not a semantic negative.

## 3. Core and Protocol equality

### 3.1 `CoreEqUnderMap`

~~~text
CoreEqUnderMap(
  admitted source Core,
  admitted target Core,
  exact total kind-preserving Core map,
  exact Core equality semantic profile)
~~~

The proposition reads every protected Core fact selected by the profile,
including where applicable:

- dependency and role declarations;
- statement, witness, challenge, randomness, object, and value occurrences;
- transcript and event order;
- claim production and use;
- reduction, check, and effect flow;
- failure, terminal, and obligation behavior; and
- the exact observation surface exported by the owner-created views.

An affirmative result establishes equality only under the named map and
profile. It does not establish Protocol equality, challenge-interpretation
equality, identical carrier bytes, identical provenance, property
preservation, or interchangeable endpoint behavior.

A complete checker may return a kind- and map-indexed disagreement as the
exact negative witness. That result is scoped to the same operands, regime,
map, and profile.

### 3.2 `ProtocolEqUnderMap`

~~~text
ProtocolEqUnderMap(
  admitted source Protocol,
  admitted target Protocol,
  exact total kind-preserving Protocol map,
  exact Protocol equality semantic profile)
~~~

This family includes the complete protected Core comparison plus challenge
interpretation. For a Fiat--Shamir Protocol it additionally compares the exact
transcript-construction meaning, including every profile-selected framing,
codec, namespace, challenge, and occurrence coordinate.

Equal `CoreId` values cannot establish Protocol equality between Fresh and
Fiat--Shamir interpretations. Equal `ProtocolId` values may supply a trivial
identity-map affirmative only under the exact matching regime and equality
profile whose laws admit that rule. Equality under a coarser observer quotient
is a separate family profile, not a cast from exact Protocol equality.

Protocol equality proves no cryptographic property. It permits a property
transport only when a separate property-specific theorem states that this
exact equality profile is sufficient and the
[transport checker](transport-composition-and-replay.md) validates every
premise and hypothesis.

## 4. Observable trace relations

### 4.1 Complete trace model

~~~text
TraceEq<O>(source, target, O, TraceModel, exact maps)

TraceRefines<S,T,O>(
  source, target, O, TraceModel, direction, exact maps)
~~~

`TraceModel` closes every coordinate that changes the trace proposition:

- event alphabet and projection;
- observer visibility and protected observations;
- source/target initial-state relation;
- public, private, and auxiliary input interpretation;
- event, value, state, and terminal maps;
- accepted, rejected, failed, aborted, and stuck observations;
- divergence and nontermination treatment;
- scheduling, fairness, and receptiveness conditions; and
- any finite, symbolic, probabilistic, or computational trace regime.

Changing any coordinate changes the model, question, or proposition. A trace
checker cannot treat omitted failure or divergence behavior as invisible by
default.

### 4.2 Equality

`TraceEq<O>` states equality of the exact observed-trace sets or
distributions specified by `TraceModel`. An affirmative result is not Core or
Protocol equality: two subjects may agree for one observer while differing in
hidden state, unobserved events, cost, probability, or other observers.

A negative requires an exact counter-trace or another family-owned refutation
accepted by a complete basis. One observed execution is not a general trace
counterexample unless the question's occurrence/model contract and rule make
that inference valid.

### 4.3 Directed refinement

The target fixes one convention:

~~~text
TraceRefines(source, target, O)
  means ObservedTraces(target, O) subseteq ObservedTraces(source, O)
~~~

The target adds no observation outside the source allowance under that exact
model. The direction is part of the question. The reverse convention,
symmetry, or conversion to trace equality requires an explicit checked rule.
Two directional judgments imply equality only when their subject, observer,
model, occurrence, map, and hypothesis coordinates are exactly compatible.

A negative refinement result identifies target behavior outside the exact
source allowance. It establishes neither the reverse direction nor
undesirability of the target.

## 5. Declared change and `ChangeConforms`

### 5.1 Declaration is not a result

`IntentionalChange` is an unauthoritative human- or policy-declared
`ChangeContract`. It records the envelope within which a successor is allowed
to differ; it does not state that the observed change is intentional,
correct, desirable, or accepted.

The admitted contract contains:

~~~text
ChangeContract {
  exact predecessor and successor subject schemas,
  protected observation relation that must remain true,
  finite permitted-delta ledger,
  exact changed event, claim, failure, terminal, and challenge occurrences,
  required unchanged maps and dependencies,
  every new property or consumer obligation created by the change
}
~~~

### 5.2 Conformance proposition

~~~text
ChangeConforms(
  admitted source,
  admitted target,
  admitted ChangeContract,
  exact observer,
  exact semantic model,
  exact maps)
~~~

An affirmative result means only that the exact source/target pair conforms to
the declared envelope. It does not prove actual human intent, policy approval,
property preservation, endpoint feasibility, or consumer acceptability.

When the exact comparison procedure is complete, an unlisted protected change
may produce a negative `ChangeConforms` proposition with the exact violating
delta. A missing view, undecidable comparison, or incomplete change map is not
that negative.

Compiler may require the admitted contract and an exact affirmative
`ChangeConforms` capability. A field called `intentional_change` containing
only the declaration grants no target eligibility.

## 6. Distributional relations

### 6.1 Exact experiment

`DistributionEq` and `DistributionClose` use explicit subdistribution
semantics. A question includes:

- source and target subjects and occurrences;
- the initial input distribution;
- shared, independent, derived, or correlated randomness;
- challenge and joint/correlation regime;
- conditioning events;
- abort, failure, retry, divergence, and missing termination mass;
- losslessness or termination assumptions;
- the measurable observation map and sigma-algebra or finite analogue;
- metric, direction, and exact bound; and
- computational resource restrictions when the relation is computational.

Abort or failure mass is never silently normalized away. A conditional
distribution is a different proposition from the corresponding
subdistribution. A coupling, hybrid, or indistinguishability proof is basis
material; the experiment and exact bound remain proposition meaning.

### 6.2 Distinct families and outcomes

Perfect equality, statistical distance, and computational
indistinguishability are distinct families or semantic regimes. Extensional
distribution equality does not establish feasible computation, low cost, or a
cryptographic property under a different adversary model.

An exact finite rational profile may admit a complete affirmative and negative
procedure. Symbolic, measure-theoretic, or computational profiles require
their exact theorem or model basis. Failure to find a coupling, distinguisher,
or proof is `CannotAnswer`; it is not a distributional negative.

A negative answer binds the exact counter-proposition and scope. For example,
an explicit event with unequal probability under a complete finite model may
refute exact equality, while a lower-bound distinguisher may refute one exact
closeness bound. Neither result widens to another input distribution,
observer, correlation regime, or metric.

## 7. Cost values and relations

### 7.1 Cost model

`CostValue` and `CostRelation` bind exact subject occurrences to one closed
cost model:

~~~text
CostModel {
  cost machine or static measure,
  input and environment regime,
  resource dimensions and aggregation,
  worst_average_amortized_or_distributional_interpretation,
  exact derivation or measurement method,
  uncertainty and sampling contract when Evidence-derived
}
~~~

Proof bytes, verifier work, prover work, memory, latency, query count,
communication, code size, and setup cost are separate dimensions. A comparison
requires an exact declared order, normalization, or unit conversion. There is
no ambient weighted score.

### 7.2 Epistemic qualification

Cost conclusions retain how they were established:

~~~text
ExactStructuralCost
ModelDerivedCost
AnalysisEvidenceDerivedEstimate
~~~

Equal numerical values do not erase these distinctions. An exact static count
does not predict runtime without an explicit cost model. A benchmark estimate
does not become a theorem merely because it uses the same unit. Measurement
enters Analysis only through an exact family rule over attributable Evidence
records or policy-qualified appraisals that preserve the producing domain's raw
observation meaning and completeness frontier together with environment,
samples, and uncertainty. The resulting `AnalysisEvidenceDerivedEstimate` is an
Analysis-owned judgment; it is distinct from an Evidence-owned
`EvidenceQualifiedEstimate`.

A complete cost relation may establish an exact order reversal as a negative
for one comparison proposition. An unavailable measurement, incomparable
dimension, or unsupported conversion is `CannotAnswer` or `Unsupported`, not
a favorable or unfavorable result.

Compiler may consume a cost capability only under a policy that names the
exact proposition, accepted epistemic kind, bound, hypotheses, assurance,
residual trust roots, source `FamilyOperationPolicyId`, exact judgment binding,
and transitive source-operation-policy closure. The Compiler use must be
permitted by the conjunction of the immediate source policy and every policy in
that closure. Analysis does not choose the optimization policy.

## 8. Relations-owned `RelationSatisfies`

> **K3 transition notice.** The ownership conclusion below remains selected,
> but its detailed consumer schema predates the K3-B rewrite of Relations.
> The durable definition, satisfaction command machine, semantic/validation
> split, operation policy, and qualified result are now owned exclusively by
> [Relation Model](../relations/relation-model.md#43-occurrence-local-satisfaction).
> Any repeated field list below is historical Analysis intake, not a second
> current Relations contract. K3-C must replace it with the minimum exact
> Analysis source manifest before this page can become a current integration
> specification.

### 8.1 Ownership decision

`RelationSatisfies` belongs to **Relations**. Predicate truth for one exact
admitted definition and instance under one occurrence-local private witness is
base relation semantics, not a derived cross-Protocol property. Analysis may
consume the result but cannot mint or reinterpret it.

The exact question, request, semantic basis, inert support instantiation,
validation basis, operation policy, invocation, qualified outcome, persistence,
and replay contracts belong exclusively to [Relation semantic
model](../relations/relation-model.md#43-occurrence-local-satisfaction). In particular,
the owner requires fresh identity- and ABI-matched premise, correspondence-
support, checker-execution, and private-witness capabilities at the checking
occurrence. An opaque definition, support record, checker identity, or public
attempt record is never executable authority.

Analysis may consume only the matching live Relations capability with the
exact definition, Interface, instance, public assignment, model, private
witness occurrence, semantic basis, exact support-instantiation ID or local
handle, validation basis, operation policy, exact request ID or local handle,
assumptions, polarity, assurance, retained facts, exact completed-source
bindings, transitive satisfaction source-operation-policy closure, named
consumer and purpose, process generation, and residual-trust closure. Its own
target policy and every Relations/source policy must permit this exact Analysis
consumer and purpose. It cannot weaken, reconstruct, or reinterpret any of
those coordinates. Correspondence or equal bytes never imply satisfaction.

### 8.2 Confidentiality and negative scope

The public record identity excludes secret witness bytes. The live
confidential capability retains the witness occurrence without creating a
globally content-addressed secret-equality oracle. Public persistence is
prohibited by default. A remote non-revealing proof of satisfaction is a
separate proof or certificate protocol; it is not serialized witness
authority.

An affirmative result states that this exact witness occurrence satisfies the
exact instance under the exact semantic model and assumptions. A negative
states only that this exact witness occurrence does not satisfy it. It does
not establish instance unsatisfiability, witness nonexistence, or failure of a
different witness.

Completeness, knowledge soundness, and other Analysis questions name an exact
Relations-owned satisfaction fact requirement and the private witness's
owner-issued unlinkable local occurrence reference when their experiment reads
relation truth. Neither coordinate is a live capability. The concrete support
instantiation cites the matching owner-private premise-record reference and its
inert `OwnerCapabilityRequirement`; the checking invocation separately supplies the
matching live satisfaction capability. That capability preserves the exact
model, semantic/support/validation bases, operation policy, request,
assumptions, polarity, assurance, completed-source bindings, transitive source-
operation-policy closure, witness occurrence, process generation, and residual
trust. The inert public attempt record is never a substitute.
Protocol-to-relation correspondence remains a separate structural result and
cannot substitute for satisfaction.

Because that premise-record reference is owner-private and nonserializable,
only coordinates whose own identity preimages name it, the witness occurrence,
or an already local child use the opaque `Local*Handle` lane defined by
[Analysis model](analysis-model.md#31-canonical-identity). In the ordinary
satisfaction-support path this makes support, derivation, judgment, and result
coordinates local. Independently defined question, proposition, semantic-basis,
and validation-basis coordinates remain portable when their own preimages do
not name the private reference. Every actual local handle is owner-instance-
and process-generation-scoped; neither it nor a digest derived from it may be
persisted or publicly disclosed. A confidential rerun with a new Relations
reference creates a new forward local-handle chain without retroactively
localizing independent public coordinates.

## 9. Cross-family implications and nonclaims

No family receives implicit subtyping from a similar name. In particular:

- Core equality does not imply Protocol equality;
- Protocol equality does not imply carrier-byte equality or every property;
- one-observer trace equality does not imply semantic equality;
- directed refinement does not imply its reverse;
- `ChangeConforms` does not imply desirability or property preservation;
- distribution equality does not imply low cost;
- equal cost under one model does not imply equal measured performance; and
- relation correspondence does not imply `RelationSatisfies`.

Cross-family reuse requires an exact typed implication or transport rule, its
subject/model/occurrence maps, side conditions, hypothesis transformation,
quantitative loss, checked basis, and exact target proposition. Failure to
apply such a rule never creates a negative target result.

This document does not claim that any direct procedure, map search, trace
model, distribution theorem, cost model, relation evaluator, or checker is
implemented, complete, correct, or formally verified. It does not establish
any relation for any concrete Protocol or relation instance, persist a live
capability, or authorize a Compiler, endpoint, release, or reliance decision.
