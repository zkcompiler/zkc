# Current Analysis--Compiler synthesis

> **Document kind:** Temporary Stage 4A reconstruction synthesis
> **Document state:** Complete for Stage 4A.1; target-neutral
> **Authority:** None. This page relates the two current reconstructions and
> the frozen Stage 3 intake. It does not repair a current disagreement, select
> a target, prove a property, establish compiler correctness, or authorize
> implementation or migration.
> **Synthesized:** 2026-08-22
> **Inputs:** [current Analysis reconstruction](current-analysis.md), [current
> Compiler reconstruction](current-compiler.md), and the frozen [Stage 4A
> entry contract](../stage-3-protocol-and-relations/stage-4a-entry-contract.md)
> **Disposition:** Absorb selected invariants, confirmed conflicts, and
> current-to-target gaps into durable owners and the Stage 4A convergence
> record; delete this page with the temporary package.

## 1. Joint reading

The current Analysis and Compiler form one coherent bounded system:

```text
admitted PIR-derived subject
  + immutable Soundness catalog and context
  + explicit derivation plan
  -> typed conditional SecurityJudgment

finite provider-defined plan domain
  -> transform and admit candidate
  -> derive candidate SecurityJudgments
  -> apply exact bound constraints
  -> score static proof bytes
  -> select deterministically
  -> recompute the submitted decision
```

This system is stronger than an optimizer that trusts transformation reports
or an analyzer that accepts attributed theorem names. Its products are narrow,
typed, and checked against immutable admitted observations. Its limitations are
therefore not well described as missing validation. They arise because one
property calculus and one compiler use case currently determine the shape of
several roles that Stage 3 has made independently meaningful.

The target-neutral conclusion is:

> Preserve the current discipline of exact subjects, closed rule bodies,
> explicit derivations, inherited hypotheses, exact arithmetic, finite
> comparison claims, and fresh recomputation under the same exact configured
> semantic authorities. Reconsider which owner
> defines each subject, relation, property, proposal, admission, assessment,
> and decision, and generalize only where an exact family requires it.

## 2. What is already architecturally strong

### 2.1 Analysis strengths

The current Soundness Kernel establishes several reusable principles:

1. Analysis occurs only over an exact admitted artifact view.
2. A rule catalog is immutable and identity-bearing; a citation does not
   become an executable rule.
3. Rule bodies form a closed syntax rather than arbitrary trusted callbacks.
4. A binding maps a general rule to exact Protocol structure but cannot choose
   an arbitrary conclusion subject.
5. A derivation is caller-supplied, acyclic, explicit, and re-checkable from
   exact inputs without trusting proof search; proof search is not confused
   with proof validity.
6. Soundness, knowledge, and completeness are notion-indexed rather than
   collapsed into a generic security flag.
7. Hypotheses are inherited monotonically and assumed judgments remain visibly
   marked.
8. Quantitative expressions use typed exact arithmetic and refuse unsupported
   symbolic forms instead of approximating silently.
9. The conclusion is conditional under its exact remaining hypotheses; it is
   not promoted into theorem truth or concrete security by execution alone.

These are semantic assets, not implementation accidents.

### 2.2 Compiler strengths

The current Compiler establishes a similarly valuable discipline:

1. Producer-owned payloads acquire authority only through exact artifact
   semantics and authentication.
2. Provider configuration and the comparison scope are explicit inputs.
3. Optimization is claimed only over one exact finite closed domain or one
   exact submitted frontier, never globally.
4. Transform execution uses immediate predecessor authority and authenticates
   each successor before later checks consume it.
5. Claim lineage is exact across retain, remove, introduce, split, merge, and
   survivor behavior.
6. Constraints consume the same Soundness evaluator rather than reimplementing
   its arithmetic or accepting provider-populated bounds.
7. Candidate-local ineligibility is separated from failures that invalidate
   the compilation attempt.
8. Objective comparison and tie resolution are deterministic.
9. `DECIDE` reconstructs the domain, candidates, validity, scores, and
   selection instead of trusting a producer's result.

The target should not trade these properties for a more convenient but less
qualified optimizer API.

## 3. The current coupling

The current model joins roles at five seams.

### 3.1 Soundness is both the Analysis architecture and one Compiler input

The only executable property calculus is the Soundness Kernel. Compiler owns
the selected Soundness context, derivation-domain providers, allowed rule and
hypothesis surfaces, bound projections, and repeated `DERIVE` calls. This is
coherent for the current KZG use case, but it makes a consumer request shape
the apparent boundary of Analysis.

Stage 4A must determine whether Analysis judgments can be identified, checked,
reused, and compared independently of one Compiler invocation while retaining
their exact subjects, contexts, hypotheses, and residual trust.

Current Compiler target properties are normally established by direct re-
analysis of each admitted candidate under that candidate's exact derivation
plan. A source judgment is re-derived separately only when a bound constraint
uses it as a lineage-scoped baseline. The current model therefore does not
transport target property truth from source property truth. Stage 4A should
retain direct target re-analysis as one valid lane and compare it explicitly
with property-specific transport rather than assuming either replaces the
other.

### 3.2 A transform provider fuses proposal with PIR-owned target admission

The PIR provider reopens an admitted predecessor, transforms it, seals it,
internally invokes PIR-owned admission, and returns an authenticated candidate.
A later family checker repeats the transformation and compares target identity.
This gives a useful replay check, but proposal construction and PIR-owned
target admission remain fused in one provider-orchestrated operation.

The frozen Stage 3 order instead distinguishes:

```text
untrusted proposal
  -> PIR-owned target authentication and admission
  -> separately qualified predecessor/successor relation
```

Stage 4A must decide the proposal and checked-transform contracts without
making a producer deterministic function the semantic definition of every
valid target relation.

### 3.3 Family-local legality stands in for a first-class relation result

Current `recognize` and `check` establish a family-specific transform trace.
`ClaimCorrespondence` provides exact lineage but explicitly is not Protocol
equality, trace refinement, distributional preservation, or a property
theorem. There is no independently named qualified predecessor/successor
relation result that another consumer can cite.

Stage 3 now supplies an exact relation architecture. Stage 4A must consume it
without converting every relation into either Compiler-local legality or an
undifferentiated preservation label.

### 3.4 Domain construction already executes semantic work

Current closed-domain construction transforms, authenticates, resolves
lineage, and enumerates derivation alternatives before returning a domain. The
same exact semantics are recomputed in later stages. This makes domain
membership authoritative but couples proposal discovery, assessment, and
comparison-domain declaration.

Stage 4A must distinguish at least:

- which possibilities a producer found;
- what set the decision claims to cover completely;
- which admitted targets and relation bases identify candidates; and
- which candidates received complete assessments.

It must preserve the current refusal to infer `NoSelection` from incomplete
search.

### 3.5 The public decision compresses its basis

The current result retains only a selected domain ordinal or `no_selection`.
That is enough for same-process recomputation with the exact context and
provider behavior. It is not an independently interpretable candidate,
assessment, comparison, or cold-replay contract.

Stage 4A must decide what a decision means before deciding whether any durable
decision object is justified. Persistence is not required merely because the
current result is small.

## 4. Confirmed current disagreements

The reconstructions identified disagreements that a target design must not
silently resolve by following code.

| Surface | Normative current account | Implemented or status-used account | Reconstruction consequence |
|---|---|---|---|
| Security quantification | Omitted from the normative index grammar | Identity-bearing `Static`, `AdaptiveInstance`, and `AdaptiveIndex` coordinate | Treat as a confirmed drift, not a selected target coordinate |
| Artifact projections | Normative grammar omits some projections | `BoundRelationAnchorCount` and `CommittedArity` are executable inputs | Re-establish an exact closed projection vocabulary in the target |
| Coverage | No clear normative Analysis owner | `ArtifactJudgment` and `DerivationCoverage` are implemented and used by status | Decide structural versus property-coverage ownership explicitly |
| Relation correspondence field | Normative and implementation shapes differ | Code and persisted forms do not match one account | Do not import either wire shape as target semantics |
| Completeness subject | Informally reads witness-in-relation meaning | `SecuritySubject` does not contain the relevant relation/model operand | Make every semantically read subject explicit |
| Security occurrence | Site influences derivation | Final `SecurityJudgment` does not retain the site | Decide whether occurrence is proposition identity, basis identity, or neither |
| Compiler exact reference encoding | Normative JSON object and generic domain tags | C++ and Python use two-element arrays and KZG-specific tags | Record as conformance conflict, independent of target encoding |

None of these disagreements proves which target alternative is correct.

## 5. Missing semantic families and outcome distinctions

The current Soundness result/refusal surface cannot express the whole Stage 4A
question space. Required families include:

- `CoreEq` and `ProtocolEq`;
- observer-indexed `TraceEq`;
- directed `TraceRefines`;
- intentional change relative to protected and permitted observations;
- distributional equality and bounded closeness;
- operational cost under an exact cost model;
- soundness, knowledge, completeness, and later property profiles;
- theorem-backed Fiat--Shamir applicability and property transport;
- property-specific composition; and
- relation satisfaction if its exact owner is selected.

These families share lifecycle concerns, but they need not share one subject
tuple, result payload, proof rule, quantitative algebra, observer model, or
meaning of a negative result.

The current outer result also compresses distinctions needed for both Analysis
and Compiler:

```text
affirmative semantic result
fact-retaining negative semantic result
unsupported question or model
cannot answer with the supplied basis
refused for missing authority or policy
malformed question, plan, or record
checker or execution failure
```

Failure to find a derivation is not a semantic negative unless the exact search
is complete for the exact question. An invalid certificate is a fact about the
certificate, not the negation of the property it attempted to prove.

## 6. Identities that are presently absent or conflated

Current structural equality and same-invocation recomputation avoid inventing
many durable identifiers. Stage 4A nevertheless needs a semantic account of
the following distinctions before choosing persistence:

### Analysis

- exact question or proposition identity;
- model and model-instantiation identity;
- hypothesis and dependency closure;
- derivation-basis identity;
- one particular derivation or certificate identity;
- qualified judgment identity;
- one checking or replay occurrence; and
- live process-local capability.

Several derivations may establish the same proposition. Several checker
occurrences may validate one derivation. Neither fact should silently change
the proposition's meaning.

### Compiler

- exact request and comparison claim;
- declared candidate-domain identity and completeness basis;
- proposal or recipe identity;
- admitted target identity;
- checked predecessor/successor relation identity;
- candidate identity, including the exact semantic path when relevant;
- per-candidate assessment identity;
- objective model and score identity;
- selection and decision identity; and
- live decision-check capability.

An ordinal alone is not a candidate identity outside the exact reconstructed
domain. The target must also decide whether two paths to the same admitted
target are one candidate or different assessed candidates; current behavior
does not answer that question generally.

## 7. Stage 3 intake pressure

The frozen Stage 3 architecture changes the available factorization without
choosing Stage 4A's answer.

Stage 3 provides:

- exact admitted Protocol, Interface, Plan, relation, construction, and
  composition subjects;
- owner-created attenuated views and complete read closures;
- process-local authority and cold replay rules;
- qualified outcome classes;
- `CheckedFSConstruction` separated from any cryptographic FS theorem;
- `CheckedCoreComposition` separated from property composition; and
- first-class checked structural relations with exact maps and bases.

Consequently Stage 4A cannot continue treating one admitted artifact view, one
Soundness subject algebra, one unchecked preservation string, or one
family-local Compiler trace as sufficient for every question. It also must not
duplicate Stage 3 admission or structural checking inside Analysis.

Stage 3 does not decide:

- the Analysis proposition and derivation architecture;
- which semantic model families v0 supports;
- how external theorem/model correspondence is established;
- the exact meaning of affirmative and negative property results;
- whether `RelationSatisfies` belongs to Relations or Analysis;
- how property-specific FS transport and composition work;
- which transform relations make candidates eligible;
- what candidate-domain completeness means beyond an exact declared scope;
- which objectives are semantic, modeled, or measured; or
- whether any Analysis or Compiler record merits persistence.

Those remain Stage 4A decisions.

## 8. Questions the candidate portfolio must answer

The equal-resolution candidates must make the following tensions explicit.

1. Is the semantic center one universal judgment language, a family-indexed
   Analysis calculus, external proof systems with adapters, or a smaller direct
   checker plus qualified certificates?
2. Which parts of question identity are common, and which remain
   property-family-specific?
3. How are exact external statements, zkc models, admitted subjects, and the
   sufficient implication between them checked?
4. Which analyses are complete decision procedures, which are proof checking,
   and which are only incomplete attempts?
5. How do probabilistic, adversarial, termination, abort, correlation, and
   resource regimes enter proposition identity?
6. Is transform production a deterministic realization function, an
   arbitrary proposal mechanism, a proof-carrying recipe, or several lanes?
7. What exactly identifies a candidate when target content, transform path,
   relation basis, and property basis may vary independently?
8. What domain forms justify `BestInDomain`, `NoSelection`, or a weaker
   feasible-choice result?
9. Which objective values are exact structural computations, model-derived
   analyses, measurements, or unavailable pending Stage 4B?
10. What can be replayed cheaply, what requires a portable proof or
    certificate, and which consumer justifies persistence?

## 9. Reconstruction exit decision

Stage 4A.1 can close when an independent audit confirms that the two detailed
reconstructions and this synthesis expose the current meanings, exercised
scope, strengths, disagreements, coupled roles, frozen Stage 3 deltas, and
remaining questions without selecting a target.

The reconstruction itself establishes no reason to preserve the current class
layout, no reason to discard it, and no migration constraint. It supplies the
baseline against which research cases and materially different candidates can
now be compared.
