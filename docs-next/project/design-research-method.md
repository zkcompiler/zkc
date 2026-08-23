# Design research method

> **Document kind:** Governance and research-method proposal
> **Document state:** Scaffold
> **Provisional owner:** `project`
> **Authority:** This page governs only the design-research process inside
> `docs-next/`. It does not alter current semantics, implementation status, or
> the product roadmap under [`docs/`](../../docs/README.md).

## 1. Purpose

The v0 program is not a defect search followed by document cleanup. It is a
reconstruction and redesign program whose result should be a coherent,
independently implementable semantic model and a complete normative corpus.

The method must therefore do two things at once:

1. preserve current decisions that remain well founded; and
2. explore better abstractions and new capabilities even when the current
   design passes every known example and test.

Testing and falsification are necessary convergence tools. They are not the
source of the complete design space.

## 2. Governing model: divergence followed by convergence

Every work package has a deliberate divergent phase and a deliberate
convergent phase.

### Divergence

Divergence reconstructs the current model, removes accidental assumptions,
collects alternatives, and asks what a better architecture could enable. It
may keep several incompatible candidates alive. Passing current tests does not
end this phase.

### Convergence

Convergence compares the candidates against exact subjects, authorities,
identities, lifecycles, consumers, composition laws, implementation
feasibility, and migration cost. It selects a provisional target only after
cross-domain review.

A later package may reopen a provisional conclusion when it discovers a new
consumer, counterexample, or capability opportunity. Reopening is explicit;
it is not silent drift.

## 3. Four required research lenses

| Lens | Question | Required result |
|---|---|---|
| **Reconstructive** | What does the current specification mean, why is it shaped this way, and how does the checkout correspond? | Current-model dossier and code/spec correspondence map |
| **Generative** | What other models are possible, and what useful capabilities could they unlock? | Design-space and opportunity map |
| **Evaluative** | Which candidates are coherent, falsifiable, implementable, compositional, and worth their migration cost? | Alternative matrix, counterexamples, and provisional recommendation |
| **Integrative** | Does the recommendation remain correct when its producers, consumers, and neighboring domains are considered together? | Cross-domain convergence record and target contract |

No package is complete after only one lens. In particular, a review that finds
no failure has not performed generative research, and a literature survey that
does not reconstruct current authority has not produced a zkc design.

## 4. Work-package cycle

### Phase A: frame the question

1. State one central architectural question.
2. Name the semantic subjects and boundaries in scope.
3. State non-goals and decisions that must remain open.
4. Identify upstream authorities, downstream consumers, and adjacent packages.
5. Choose representative scenarios and opportunity prompts.

The unit of work is a semantic question or transition, not a directory or a
large source file.

### Phase B: reconstruct the current model

6. Read the exact current normative owners and record any conflicts without
   choosing by recency.
7. Reconstruct object roles, identities, authorities, environments, binding
   times, transitions, refusals, and non-claims.
8. Trace the corresponding implementation types, registries, APIs, passes,
   checkers, tests, and examples.
9. Recover historical rationale only where it explains a live constraint;
   history never overrides the current owner.
10. Produce a current-model dossier that another reviewer could challenge.

Code is inspected before redesign to reveal real boundaries, feasibility, and
implicit assumptions. It is not allowed to decide intended semantics merely by
existing.

### Phase C: expand the design space

11. Generate a candidate portfolio rather than one favored rewrite.
12. Ask capability and option-value questions, not only failure questions.
13. Study primary research, official specifications, and relevant systems
    against the exact local question.
14. Construct new examples, future-consumer probes, and clean-room designs.
15. Record what each candidate makes easier, harder, newly possible, or
    permanently excluded.

### Phase D: evaluate and converge

16. Apply representative scenarios, counterexamples, and boundary pressure.
17. Compare semantic clarity, authority, identity, expressiveness,
    compositionality, independent implementability, evolution, and cost.
18. Review the candidate with every affected producer and consumer domain.
19. Select a provisional target, defer the choice with exact missing evidence,
    or preserve the current model with a positive rationale.
20. State reversal conditions and residual open alternatives.

### Phase E: promote and reconcile

21. Write the target contract in its durable normative or architectural owner.
22. Record a decision when alternatives and rationale remain useful.
23. Update the global architecture only with conclusions the package actually
    establishes.
24. Produce a current-to-target implementation gap map without changing code
    to make the gap disappear.
25. Remove absorbed material from temporary notes and route intentionally
    deferred work to the single global roadmap.

Implementation changes normally begin after the affected target contract is
stable. A feasibility prototype may occur earlier, but it remains isolated,
non-authoritative, and explicitly disposable until a design is selected.

## 5. Candidate-portfolio rule

For every material design question, investigate these candidate classes when
they are meaningful:

1. **Preserve:** retain the current design and make its rationale explicit.
2. **Complete or align:** preserve the design while filling missing roles,
   definitions, or owner alignment.
3. **Structural redesign:** change the subject, authority, lifecycle, or
   boundary model.
4. **Capability-expanding design:** accept a larger change because it enables a
   valuable new use, composition, checker, carrier, analysis, transform, or
   realization mode.

The portfolio is not a quota. A class may be impossible or redundant, but the
package must say why rather than silently omitting it. The current design is a
candidate, not the default winner; novelty is also not a reason to choose a
replacement.

## 6. Generative opportunity prompts

Each package asks a relevant subset of these questions:

- If the current carrier, API, or directory structure did not exist, what
  semantic model would we choose?
- What stable subject would an independent implementation or checker consume?
- What becomes possible with a second relation source, analysis calculus,
  transform family, carrier, endpoint kind, or realization target?
- Can several special cases become one smaller principle without weakening
  their distinctions?
- Which current global choice could become a typed local choice?
- Which current local convention actually affects global identity or
  authority?
- What new composition, caching, exchange, validation, or reuse becomes
  possible under a different boundary?
- Which future option would be expensive or impossible if v0 fixes the current
  model?
- Can a new capability remain an extension boundary rather than entering the
  v0 kernel?
- What would a clean-room designer build after reading only the intended
  semantics and consumer requirements?

An opportunity is not automatically a requirement. Record its value,
prerequisites, costs, and latest responsible decision point.

## 7. Source and authority discipline

Use sources in this order for their own questions:

1. current documentation authority map;
2. exact normative owners;
3. architecture, status, roadmap, and evidence, each within its authority;
4. implementation and tests as correspondence and feasibility evidence;
5. primary research and official external specifications as design input; and
6. prior notes as non-authoritative rationale and candidate history.

External work may reveal an abstraction, theorem shape, checker boundary, or
counterexample. Every research citation must also state the limit of the
analogy. It cannot establish zkc conformance, discharge local assumptions, or
ratify a design decision by reputation.

## 8. Representative scenario portfolio

Scenarios are architecture probes, not the definition of the supported
language and not evidence of general correctness. A package selects the
smallest portfolio that exercises its decision.

| Scenario family | Architectural pressure |
|---|---|
| Minimal closed Sigma-style protocol | Small complete transcript, claim flow, seal, analysis, and verifier path |
| Relation-bound protocol such as R1CS | External relation identity, public instance, witness interface, and opaque grounding |
| Reduction-heavy protocol such as Sumcheck | Multi-round claim transformation, challenge structure, residual obligations, and property analysis |
| Lookup or FRI-style protocol | Committed-object declarations, uneven shapes, routes, and incomplete endpoint surfaces |
| KZG batching transform | Compiler predecessor/successor identity, candidate construction, replay checking, and property constraints |
| Prover/verifier endpoint pair | Asymmetric projection, proof ABI, witness capability, observable effects, and supplier boundaries |
| Linked or composed protocol | Identity, transcript splice, relation mapping, assumptions, and property transport |
| Imported verifier or recursion candidate | Descent, bounded verification, outer relation material, and explicit deferred capability |

The portfolio may grow when a new design creates a previously impossible use.
It must not become a fixed benchmark that biases every abstraction toward the
current examples.

## 9. Evaluation axes

A converging candidate is assessed on all applicable axes.

| Axis | Question |
|---|---|
| Semantic clarity | Does it define one exact subject and avoid hidden meanings? |
| Authority | Are definition, proposal, checking, and reliance powers explicit? |
| Identity | Are preimages, versions, environments, and identity changes exact? |
| Lifecycle | Are creation, mutation, admission, supersession, and refusal coherent? |
| Expressiveness | Does it represent current and credible future protocols without ad hoc exceptions? |
| Capability | What valuable behavior becomes newly possible or materially easier? |
| Conceptual compression | Does it replace repeated special cases with a smaller sound principle? |
| Compositionality | Do identities, assumptions, effects, failures, and obligations compose explicitly? |
| Independent implementability | Can another implementation or checker reproduce the contract without consulting current code? |
| Extensibility | Can new entries be added at the right layer without changing a kernel unnecessarily? |
| Evolution | Does it preserve future options and make incompatible changes visible? |
| Feasibility | Can the current implementation migrate without making code the semantic authority? |
| Evidence boundary | Are observations and support claims kept distinct from meaning? |
| Cost | Are complexity, dependency, migration, and maintenance costs proportionate to the gain? |

No scalar score decides the design. Tradeoffs remain explicit, and a candidate
that fails an identity or authority requirement cannot compensate with
implementation convenience.

## 10. Research states

Use these states for design conclusions:

- **observed:** directly reconstructed from its current owner or implementation;
- **hypothesis:** a possible explanation, abstraction, or opportunity;
- **candidate:** a sufficiently concrete alternative for comparison;
- **viable:** survived local evaluation but not cross-domain convergence;
- **provisional:** selected for dependent research but explicitly reopenable;
- **ratified:** accepted into its durable owner through the eventual authority
  process;
- **rejected:** not selected, with a rationale worth retaining; and
- **deferred:** deliberately left to a later decision point with a trigger.

These research states do not replace document state, normative maturity, or
implementation status.

## 11. Parallelism and convergence

Independent tracks may perform reconstruction, literature review, code
mapping, scenario analysis, candidate generation, and feasibility experiments.
They may not independently ratify shared identities, authorities, admission
rules, bridge ownership, preservation relations, version rules, or public
names.

Parallel work begins from a shared provisional boundary contract and returns
to one convergence review. If two local designs require incompatible shared
assumptions, the shared boundary is reopened rather than choosing by schedule.

## 12. Package outputs and gates

Every substantial package produces:

```text
central question and non-goals
current-model dossier
code/spec correspondence map
consumer and dependency map
design-space map
opportunity map
candidate and alternative matrix
scenario and counterexample results
provisional conclusion and reversal conditions
target contract or explicit deferral
current-to-target implementation gap
temporary-note absorption record
```

Progress is gate-based rather than calendar- or document-count-based:

1. **Discovery gate:** current design, alternatives, opportunities, and source
   limits are sufficiently covered.
2. **Local coherence gate:** the preferred candidate has exact subject,
   authority, identity, lifecycle, transition, refusal, and non-claims.
3. **Convergence gate:** affected producers and consumers can share the
   boundary without contradictory assumptions.
4. **Normative-readiness gate:** a clean-room implementation can be written
   from the target contract, and migration effects are explicit.
5. **Implementation-readiness gate:** the implementation gap can be reviewed
   without using code to reinterpret the target.

Passing a current test suite is evidence within these gates. It is never the
definition of design completeness.
