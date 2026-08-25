# Protocol Property Analysis

> **Document kind:** Domain index
> **Document state:** Active target-domain index
> **Target alignment:** Selected Stage 4A federated typed Analysis target
> **Provisional owner:** `analysis`
> **Authority:** None during the transition. Current property calculus remains
> governed principally by the [Soundness Kernel specification](../../docs/spec/soundness.md).
> **Closure interpretation:** This index records a selected package-resolution
> target. `Selected`, `target`, and `exact` describe intended role, scope, and
> ownership; they do not assert integrated definition closure or semantic
> freeze. The [v0 Semantic Design Program](../project/v0-design-program.md#14-progress-and-change-control)
> owns the live gate.

## Purpose

`analysis/` owns reusable post-admission evaluation of properties over exact
subject tuples. Admitted semantic subjects, source-owned immutable views, and
later-owned occurrence or model inputs remain separately typed; none is widened
into a universal admitted fact root. The domain's center is a typed calculus of
questions, subjects, indices, rules, hypotheses, derivation plans, checked
derivations, and qualified judgments—not a generic home for every check or
inference rule in zkc.

The domain name describes the semantic service. `Judgment` remains the formal
name for its typed conditional outputs; other domains retain ownership of their
own structural, correspondence, compilation, and validity judgments.

## Owns

- exact property subjects and analysis sites;
- security tracks and notions, including soundness and knowledge variants;
- completeness as a separate property track over shared typed machinery;
- future zero-knowledge or other property tracks only if they fit the same
  subject and derivation model;
- typed result schemas, exact quantities, bounds, and resource variables;
- hypotheses, assumptions, external propositions, and inherited obligations;
- rule and signature schemas, premise bindings, catalogs, and application;
- explicit derivation plans, plan checking, and independently re-checkable
  results;
- exact property-subject selection, including Interface, Plan, relation, OIR,
  target, supplier, or later-owned occurrence inputs only when the question
  names them and declares their complete read set;
- `FSCompile` as a theorem- or model-backed judgment over exact admitted Fresh
  and Fiat--Shamir Protocols, the exact `AdmittedTranscriptConstruction`, and
  the affirmative exact `CheckedFSConstruction` that retains its maps and
  regime, together with the question's model, rule, assumptions, and
  quantitative parameters;
- property-specific `PropertyTransport` over an exact source judgment, an exact
  affirmative checked source/target relation, the property-specific rule,
  hypotheses, substitutions, and losses;
- property-specific composition over exact admitted children and target, an
  exact admitted `CoreCompositionSpec`, and an affirmative exact
  `CheckedCoreComposition`, without importing a property from structural
  composition alone;
- exact property-coverage accounting that preserves unproved, unsupported, and
  inapplicable members instead of creating a universal verified state; and
- purpose-bound persistence, cold replay, cache classification, disclosure,
  local-taint propagation, and residual-trust closure for Analysis results.

## Does not own

- PIR formation, `WF`, linearity, binding, closure, authentication, admission,
  or link;
- relation interface correspondence merely because it is written as a
  judgment;
- compiler `DOMAIN`, legality, scoring, selection, or decision checking;
- OIR validity, projection coverage, or abstract execution verdicts;
- the truth of an external theorem or hypothesis named by a rule;
- Protocol construction, including deterministic formation and admission of a
  Fiat--Shamir Protocol;
- the source-owned definitions or authenticated views from which analysis
  reads facts;
- formalization receipts, tests, or conformance observations; or
- a universal “verified” state that collapses distinct properties.

## Dependencies

- `foundation/` for exact identity, authority, and admission mechanics;
- `pir/` for exact admitted Protocol subjects and purpose-specific authenticated
  views of their events, schedule, values, objects, randomness, challenges,
  claims, checks, failures, terminals, obligations, dependencies, occurrences,
  and challenge interpretation, plus an exact admitted
  `TranscriptConstruction`, affirmative `CheckedFSConstruction`, admitted
  `CoreCompositionSpec`, affirmative `CheckedCoreComposition`, or exact
  Interface/Plan view only when the family question or rule names that
  structural satellite or result;
- `relations/` for exact admitted relation operands and exact question-scoped
  A/N checked comparison, grounding, or correspondence capabilities whose read
  closure contains every relation fact the question consumes, plus live
  `CheckedRelationSatisfaction` authority and its distinct owner-private premise-
  record and witness-occurrence references when a completeness, knowledge, or
  other experiment reads confidential relation truth; and
- conditionally, `evidence/` for exact attributable records and policy-qualified
  appraisals when, and only when, an explicit family rule names those inputs.

Evidence is not an ambient dependency of subject identity. A family that does
not declare an exact Evidence-derived basis neither reads Evidence nor changes
its question, proposition, or ordinary derivation semantics because Evidence
records exist.

The calculus must not read mutable or producer-asserted mirrors where its
contract requires facts reconstructed from an admitted subject through its
source-owned authenticated view.

Each source domain owns its narrow authenticated view and defines what every
exported fact means. Analysis owns the question-specific adequacy requirement,
logical evaluation, derivation checking, and resulting judgment. A view is not
a universal fact root, and adding an ambient read changes the analysis
contract.

## Consumers and outputs

- `compiler/` consumes typed results and exact judgment capabilities in
  constraints and objectives without reimplementing their meaning;
- `project/` may summarize supported property tracks through global status;
- `evidence/` records receipts, source readings, parity, and checks supporting
  implementation or theorem-correspondence claims; and
- guides explain how to request and interpret a result.

A property result remains conditional on its stated hypotheses and exact
subject. Consumers cannot widen the subject, erase inherited obligations, or
use its authority outside the conjunction of the exact
`FamilyOperationPolicyId` and every transitive source-owner operation policy
bound to the result.

Any result derived from a Relations owner-private premise record or witness-
occurrence reference uses the corresponding Analysis `Local*Handle` values rather than portable
content IDs. Compiler or another named consumer may use it only inside the same
owner-authorized process and purpose. Compiler's own local-dependency taint then
begins at the first Compiler value whose own preimage names that local result,
normally a qualification projection, assessment portfolio or use record,
constraint, objective, assessment, or decision. A candidate or domain is local
only if its own transition, path, or domain preimage names a local semantic
child. Every actually affected forward chain is nonpersistable and has no exact
cold replay.

An occurrence-sensitive question cites the exact later-owned execution or
observation occurrence and the exact Stage 3 invocation or observation tuple to
which it is bound. Stage 3 mints no runtime-occurrence subject, and one observed
execution cannot be generalized without a separately stated model and rule.

Outcomes are qualified rather than Boolean and preserve the common classes when
applicable:

```text
Affirmative
Negative(reason, retained_facts)
Unsupported(exact unsupported question or construct)
CannotAnswer(missing named semantic input or basis)
Refused(missing authority or prohibited invocation)
Malformed(exact input framing or structural defect)
CheckerFailure(operational failure with no semantic conclusion)
```

A complete decidable query may return a successful negative judgment. Failure
to find a derivation is not negative truth without a completeness theorem. Only
completed A/N results mint their exact question-, polarity-, assurance-, family-
operation-policy-, transitive-source-policy-closure-, and completed-judgment-
binding-scoped capability. That capability also retains the complete
`ExactCheckedResultAuthorityBinding<Analysis,F>` and its inert
`OwnerCapabilityRequirement`; an affirmative-only premise requires the
affirmative variant. Quantitative and conditional judgments retain their own
result forms.

## Bridge ownership

The source domain owns authenticated fact-view construction and every exported
fact's definition. `analysis/` owns selection of the exact property subject,
the finite read vocabulary required by the question and basis, derivation-plan
checking, and the resulting judgment. Judgment consumption in compiler
constraints belongs to `compiler/`, which must cite result meaning rather than
restate it.

Fiat--Shamir construction, `FSCompile`, and `PropertyTransport` are separate
contracts. An admitted FS Protocol may exist without an `FSCompile` judgment,
and `FSCompile` does not transport every property. Only an Analysis-owned,
property-specific transport rule may derive the exact target judgment and its
changed hypotheses or quantitative loss.

## Target documents

- [Selected Analysis and Compiler Architecture](../project/analysis-and-compiler-architecture.md)
- [Analysis Semantic Model](analysis-model.md)
- [Semantic Relation Families](semantic-relations.md)
- [Cryptographic Property Families](cryptographic-properties.md)
- [Transport, Composition, and Replay](transport-composition-and-replay.md)

These pages are durable non-normative Stage 4A candidate targets at package
resolution. The current Soundness Kernel and related specifications under
`docs/` remain authoritative until explicit normative consolidation and
cutover.

## Reopened integrated-closure and later work

Stage 4A selected a family-indexed question/proposition model, profile and
basis boundaries, support and validation identities, qualified outcomes,
property-family topology, Fiat--Shamir applicability, transport, composition,
coverage, replay, trust, and extension law at its then-current package
resolution. Post-selection revalidation reopened the causal strategy/history
interface, primary-source theorem and model grounding, the single shared
Fiat--Shamir structural read contract, and authenticated quantitative
occurrence and loss hooks. Those are pre-freeze consumer questions; they do not
require completing every theorem family. Later work still includes concrete
theorem libraries, external proof systems, certificate formats, checker
implementations, supported theorem instances, cryptographic assumptions, and
implementation organization.

Stage 4B may add exact OIR-, realization-, or endpoint-owned subjects only
through explicit family profiles and complete read contracts. Stage 5 tests
the joined capability surface. Evidence and reliance remain separately owned;
Stages 7 and 8 retain normative consolidation, implementation architecture,
conformance, and migration.
