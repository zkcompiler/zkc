# Stage 4A Analysis and Compiler charter

> **Document kind:** Temporary design-research charter
> **Document state:** Satisfied Stage 4A charter; Stages 4A.0--4A.5 complete
> **Authority:** None. This charter bounds research. It does not define an
> Analysis or Compiler judgment, establish a property or compilation result,
> report implementation correspondence, authorize migration, activate Stage
> 4B, or change current normative authority.
> **Activated:** 2026-08-22
> **Satisfied:** 2026-08-22
> **Frozen input:** Completed Stage 3 durable target owners and the bounded
> Stage 4A entry contract produced by the Stage 3 package.
> **Disposition:** Absorb reviewed conclusions into `analysis/`, `compiler/`,
> and exact shared owners; delete this charter with the temporary package before
> documentation cutover.

## 1. Activation decision

Stage 4A is activated as an Analysis-then-Compiler design-research branch.
Activation closes only Stage 4A.0: it confirms the frozen intake, first bounded
question tranche, work sequence, required outputs, validation program,
reopening rules, and exit gate.

Activation does not imply agreement with a generic judgment envelope, a
particular security calculus, `RelationSatisfies` ownership, a theorem prover,
proof-object format, Compiler pipeline, transform-provider model, selection
policy, or persistence design.

The first bounded Analysis tranche covers exact observer-indexed structural and
trace questions:

- `CoreEq` and `ProtocolEq`;
- `TraceEq[O]`;
- directed `TraceRefines[source, target, O]`; and
- `IntentionalChange` over exact protected observations and effects.

It must determine the common question, subject, map, model/rule, assumption,
read-closure, derivation, qualified-result, capability, and replay boundary. It
must not assume that distributional or cryptographic properties fit the same
result algebra merely because they reuse some fields.

## 2. Central question

How should zkc define independently interpretable and re-checkable Analysis
judgments over exact admitted Protocol, Interface, Plan, relation, construction,
composition, and later occurrence subjects, and then define a Protocol compiler
that consumes those exact judgments while keeping proposal, target admission,
semantic relation, legality, optimization, and decision authority separate?

The answer must support interactive and non-interactive ZK protocols. It must
preserve observer-indexed traces, probabilistic and adversarial models,
assumptions and quantitative losses, Fiat--Shamir and composition premises,
negative and indeterminate outcomes, finite candidate-domain claims, and
deterministic replay without inventing a universal `verified` state.

## 3. Frozen intake

The following Stage 3 decisions are fixed unless Section 13 is satisfied.

### 3.1 Subjects, views, and authority

1. Analysis consumes exact `AdmittedProtocol` subjects or explicitly attenuated
   owner-created views. A view never becomes a second Protocol representation.
2. Interface-, Plan-, relation-, OIR-, target-, supplier-, or occurrence-
   sensitive questions cite every extra subject and a complete read set.
3. `AdmittedPlan` is distinct from affirmative `CheckedPlanRealizes`; structural
   coverage authority is required only when the question actually depends on
   it.
4. Relation definition, admitted relation subjects, artifact observations,
   correspondence, grounding, satisfaction, and cryptographic properties are
   distinct.
5. Live authority is process-local. IDs, bytes, signatures, theorem names,
   proof-assistant files, result records, and provenance do not mint it.
6. External model, theorem, rule, algorithm, and checker references are typed by
   exact owner, semantic regime, identity, ABI or statement, and dependency
   closure.
7. A result may be persisted only after a named independent consumer justifies
   complete basis identity and cold replay. Serialization never preserves a
   live capability.

### 3.2 Required named relations

Stage 4A must preserve rather than collapse:

- Core and Protocol equality;
- observer-indexed trace equality and directed refinement;
- distributional equality or bounded directional closeness;
- intentional semantic change;
- cost relations under an exact model;
- notion-specific soundness, knowledge, completeness, and any selected later
  property;
- relation satisfaction if and only if its ownership and model boundary are
  resolved;
- Fresh-to-Fiat--Shamir structural construction versus theorem-backed
  `FSCompile`;
- property-specific transport;
- structural Core composition versus property composition; and
- Compiler predecessor/successor relations versus target admission, legality,
  constraint satisfaction, scoring, and selection.

### 3.3 Fiat--Shamir and composition inputs

1. `FSCompile` begins only from admitted Fresh and Fiat--Shamir Protocols, the
   exact admitted transcript construction, and affirmative
   `CheckedFSConstruction` retaining exact maps and regime.
2. `FSCompile` states its transcript/hash model, oracle or other assumptions,
   challenge treatment, failure/abort conditioning, observer set, parameters,
   and quantitative loss. It transports no property by default.
3. Property composition begins only from independently admitted children and
   target, an admitted composition specification, and affirmative
   `CheckedCoreComposition` with resolved maps.
4. Shared, joint, imported, derived, and substituted randomness; captured
   failures and reaches; suppression; terminal combination; and intentional
   changes remain explicit property premises when read.

### 3.4 Compiler ordering and authority

The fixed order is:

```text
provider request + admitted predecessor
  -> unauthoritative successor proposal
  -> PIR authentication and independent target admission
  -> exact predecessor/successor relation check
  -> constraints and objectives over exact qualified inputs
  -> deterministic selection over one declared complete finite domain
  -> qualified Compiler decision
```

Compiler policy cannot define Analysis meaning. Selection cannot create a
Protocol, relation, or transported property. A positive eligibility premise
requires the exact affirmative capability. `NoSelection` over a complete domain
is distinct from incomplete search, unsupportedness, refusal, malformed input,
or checker failure.

## 4. Ownership and ordered seams

`analysis/` owns:

- Analysis questions and exact subject tuples;
- observer, direction, result, and quantitative indices;
- model, theorem/rule, assumption, hypothesis, substitution, and loss bases;
- derivation plans, direct checks, validation, qualified judgments, and their
  exact authority;
- equivalence, refinement, distribution, intentional-change, cost, and selected
  property-family meanings;
- theorem- or model-backed `FSCompile`;
- property-specific `PropertyTransport`; and
- property composition after an affirmative structural composition premise.

`compiler/` owns:

- transform-family requests, unauthoritative plans/proposals, and lineage;
- finite candidate domains and exact completeness claims;
- orchestration of target authentication/admission and exact transform-family
  relation checking without owning either predicate;
- compiler-local legality;
- constraints over exact relation and Analysis outcomes;
- objectives, score domains, comparison, ties, selection, `NoSelection`, and
  decision replay; and
- transform profiles that genuinely belong below the Compiler owner.

PIR retains Protocol authentication/admission. Relations and other named bridge
owners retain predecessor/successor relation meaning. Stage 4B retains OIR,
projection, realization, and endpoint-feasibility results. Evidence retains
observations and claim support; consumers retain reliance decisions.

`RelationSatisfies` remains unoffered until the package decides whether its
semantic owner is Relations or Analysis. Either candidate must preserve an
occurrence-local witness capability, exact definition and instance, model and
assumptions, qualified outcomes, and the non-implication from correspondence.

## 5. Explicit non-goals

Stage 4A does not:

- implement, refactor, optimize, or migrate the checkout;
- make `docs-next/` normative or change current owners under `docs/`;
- prove theorem truth, model adequacy, checker correctness, soundness,
  knowledge, completeness, zero knowledge, Fiat--Shamir security, composition
  preservation, transform correctness, or optimality;
- select a proof assistant, theorem prover, SMT solver, optimizer, backend,
  cryptographic assumption, or transform family by ecosystem popularity;
- make one calculus universal merely because several families share fields;
- allow derivation search failure to mean a negative judgment without an exact
  completeness theorem;
- let theorem citations, proof files, tests, receipts, signatures, registries,
  or loaded host functions stand in for exact correspondence and authority;
- let provider enumeration or ambient state define a complete candidate domain;
- let a Compiler result imply target admission, semantic preservation,
  property transport, endpoint feasibility, or runtime support;
- finalize Stage 4B, Evidence, reliance, normative cutover, or implementation
  architecture; or
- optimize the target design for migration convenience.

## 6. Research sequence

### Stage 4A.0: activate and bound

Reconcile the completed Stage 3 entry contract with durable owners, name the
first Analysis tranche, publish this charter and package index, update live
program routing, and state exactly what remains undecided.

**State:** Complete.

### Stage 4A.1: reconstruct

Reconstruct current Analysis and Compiler specification authority,
implementation, tests, examples, status, and history. Record exact subjects,
identities, assumptions, rules, plans, transitions, outcomes, authority,
persistence, consumers, conflicts, and unknowns without choosing by current
class structure or repairing disagreement by implication.

**State:** Closed after independent reconstruction audit.

### Stage 4A.2: expand

Derive zkc-native design forces and capability opportunities. Study primary
research and official systems for cryptographic program logics, probabilistic
relational reasoning, theorem/model correspondence, proof objects and replay,
verified and validation-backed compilation, equality saturation,
superoptimization, finite-domain selection, and proof-carrying transforms.
Record both useful mechanisms and path-dependent constraints.

**State:** Complete.

### Stage 4A.3: instantiate Analysis candidates

Produce equal-resolution Analysis architectures covering the first tranche and
all required later families. Each must close subjects, identities, views,
models/rules, assumptions, derivations, checking, qualified outcomes,
capabilities, replay, persistence, FS, composition, relation satisfaction, and
Compiler-facing exports. Select a provisional Analysis model only after
scenario and producer/consumer review.

**State:** Complete after equal-resolution portfolio and integrated scenario
audit.

### Stage 4A.4: instantiate Compiler candidates and converge jointly

Produce equal-resolution Compiler architectures over the provisional Analysis
model. Close requests, domains, proposals, target admission, exact step
relations, legality, constraints, objectives, comparison, selection,
`NoSelection`, checking, identity, replay, persistence, and trust. Feed exact
read-set or result insufficiencies back to the affected Analysis decision, then
converge the ordered pair.

**State:** Complete after joint D/Q, assessment, decision, and peer-boundary
convergence audit.

### Stage 4A.5: promote and exit

Promote reviewed conclusions into durable Analysis, Compiler, and exact shared
owners; update the global architecture and program state; record current-to-
target gaps without migration planning; reconcile the Stage 4B peer boundary;
account for every temporary input; and pass independent semantic and
documentation exit audits.

**State:** Complete; durable promotion, absorption accounting, and independent
exit audit CLEAN and CLOSED.

## 7. Required work products

Stage 4A cannot exit without independently reviewable coverage of:

1. current Analysis and Compiler specification/code/test/example
   reconstruction;
2. current authority, conflict, unknown, and current-to-Stage-3 seam maps;
3. zkc-native design forces, option-value opportunities, and falsifiers;
4. primary-source Analysis, cryptographic-theory, Compiler, and transformation
   cases with explicit transfer limits;
5. at least four materially different integrated candidates at equal
   resolution, including preservation, completion/alignment, structural
   redesign, and capability-expanding controls;
6. exact Analysis question, subject, view, model, theorem/rule, assumption,
   derivation, result, identity, authority, outcome, replay, persistence, and
   residual-trust contracts;
7. exact equality, trace, refinement, distribution, intentional-change, cost,
   selected property, `FSCompile`, property-transport, composition-property,
   and relation-satisfaction decisions or bounded deferrals;
8. exact Compiler request, domain, proposal, target-admission, checked-step,
   legality, constraint, objective, comparison, selection, `NoSelection`,
   decision, replay, and persistence contracts;
9. identity, dependency, assumption, observer, read-set, authority, outcome,
   producer/consumer, persistence, checker, trust, and extension matrices;
10. integrated scenarios, laundering probes, opportunity tests, counterexamples,
    and reversal triggers;
11. explicit Stage 4B peer reconciliation and any bounded handoff;
12. convergence, alternative dispositions, current-to-target gap, durable
    promotion, absorption, and exit-audit records.

Files are created when work begins, not as empty placeholders. Several outputs
may share a page when their roles remain independently traceable.

## 8. Candidate discipline

Every material candidate answers the same axes:

```text
semantic center and owned subjects
question and result families
identity and dependency closure
views, read sets, and adequacy
models, theorems, rules, assumptions, and external correspondence
derivation or direct-check authority
qualified outcomes and negative meaning
capabilities, persistence, cold replay, and residual trust
Fiat--Shamir, transport, relation, and composition seams
Compiler requests, finite domains, candidates, relations, and decisions
extension and unknown-question behavior
Stage 4B and Evidence consumers
```

At least one candidate preserves the current conceptual model, one completes or
aligns it, one changes the subject or authority structure, and one enables a
materially new capability. External systems are cases, not votes. A favored
candidate cannot be selected before equal-resolution controls exist.

## 9. Initial scenario portfolio

The portfolio includes at least:

1. structurally equal Protocols with an incomplete or ill-typed map;
2. trace equality under one observer set but not another;
3. directed refinement with intentional verifier-visible change;
4. distributional closeness with abort or failure probability mass;
5. a conditional soundness judgment with explicit inherited hypotheses and a
   quantitative bound;
6. an unsuccessful derivation search without a completeness theorem;
7. an external theorem citation or proof-assistant artifact without established
   theorem/model correspondence;
8. admitted Fresh and Fiat--Shamir Protocols with affirmative structural
   construction but unavailable `FSCompile` basis;
9. two property transports over one structural relation with different
   assumptions and losses;
10. property composition with shared challenges, child occurrences, and an
    intentional change;
11. one relation instance and two occurrence-local private witness assignments,
    including unresolved `RelationSatisfies` ownership;
12. an identity-preserving proposal and a content-changing proposal;
13. a well-formed proposal whose target admission fails;
14. an admitted target with negative, unsupported, or unavailable
    predecessor/successor relation results;
15. a negative Analysis result used by an explicitly negative constraint but
    rejected from affirmative eligibility;
16. an incomplete provider search that cannot produce `NoSelection`;
17. a complete finite domain with deterministic equal-score tie handling;
18. endpoint feasibility absent from a request and therefore not a hidden
    rejection criterion; and
19. serialized derivation or decision data that cannot carry live authority
    across process reset.

Every scenario records exact inputs and authorities, requested relation,
qualified result, identity and capability effects, residual assumptions,
consumer behavior, and a falsifier. New candidates may add opportunities that
the current design cannot express.

## 10. External research discipline

Use primary papers, official specifications, and source repositories. For each
case record:

- the exact problem and semantic object;
- what is normative, mechanized, proved, validated, tested, or merely
  implemented;
- authority and trusted-computing-base placement;
- theorem, model, assumption, proof-object, checker, and replay boundaries;
- candidate-domain and search-completeness meaning where applicable;
- design strengths and difficult-to-reverse accumulated constraints;
- precise zkc transfer candidates; and
- the limit of every analogy.

No external theorem or mechanization establishes a zkc property. No system is
selected by adoption, maturity, or reputation alone.

## 11. Stage 4A.0 exit gate

Stage 4A.0 is complete because:

- Stage 3 is CLEAN and CLOSED and its frozen target, durable owners, Analysis
  handoff, and Stage 4B peer handoff are stable;
- this charter names the first bounded Analysis tranche and the whole-branch
  question families;
- Analysis precedes Compiler selection while Compiler reconstruction and
  research may supply consumer pressure;
- required work products, scenarios, research discipline, reopening, and exit
  gates are explicit;
- at activation, live program and temporary-workspace routing identified Stage
  4A as active; and
- no Analysis/Compiler target, property result, implementation, migration,
  Stage 4B activation, or normative cutover is claimed.

## 12. Whole-Stage exit gate

Stage 4A exits only when a clean-room reader can reconstruct the selected
Analysis and Compiler contracts without current class names, ambient
registries, provider state, or undocumented theorem assumptions; every
question and transition has exact subjects, identities, views, bases,
assumptions, outcomes, authority, replay, and residual trust; Analysis meaning
is independent of Compiler policy; Compiler decisions range only over exactly
admitted and related candidates in a declared complete domain; all required
scenarios pass; Stage 4B shared boundaries are reconciled; and reviewed
conclusions are promoted without durable dependency on individual temporary
notes.

Closure is a bounded design result. It does not establish theorem truth,
cryptographic security, compiler correctness, implementation conformance,
optimality beyond an exact finite domain, migration readiness, or normative
authority.

The gate is satisfied. A clean-room reader can reconstruct the selected
family-indexed Analysis and five-plane validated-decision Compiler from the
durable owner pages; all thirty-nine scenarios and chartered matrices close;
the Stage 4B peer boundary is reconciled without activation; and the
absorption and exit records account for every temporary input and durable
destination. Exact snapshot hashes and documentation checks are recorded in
the [convergence](convergence.md) and [exit audit](exit-audit.md).

## 13. Reopening and change control

A frozen Stage 3 decision may be reopened only by an exact counterexample,
authority or identity contradiction, impossible clean-room interpretation, or
materially better capability whose costs and affected consumers are explicit.
In particular, downstream convenience, theorem-prover encoding, provider API,
optimizer state, score, test behavior, or current implementation shape is not a
reopening reason by itself.

Every reopening record names:

```text
contradicted decision and falsifying evidence
affected subjects, regimes, identities, and views
authority, assumption, observer, outcome, and replay consequences
at least one equal-resolution alternative
affected Analysis, Compiler, Stage 4B, Evidence, and reliance consumers
new compatibility or wire commitment, if any
documents and checks requiring re-review
```

Reopening pauses only the affected conclusion and its dependents. It cannot be
hidden in generic metadata, a widened result, an implicit provider default, a
theorem citation, a score, or a compiler exception.
