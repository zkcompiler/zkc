# Stage 4A: Analysis and Compiler Co-design

> **Document kind:** Temporary design-research package index
> **Document state:** Completed Stage 4A research package; retained for the
> bounded Stage 4B handoff and deletion accounting
> **Provisional owner:** `analysis`, followed by `compiler`, with shared
> boundary coordination owned by `project`
> **Authority:** None. This package cannot define a normative judgment, admit a
> subject, mint a capability, report implementation support, authorize
> migration, activate Stage 4B, or establish a property or compilation result.
> **Activated:** 2026-08-22
> **Completed:** 2026-08-23
> **Current boundary:** Stage 4A.0--4A.5 are complete. The selected federated
> Analysis and validated-decision Compiler are promoted into durable
> non-normative target owners. Stage 4B remains unactivated.
> **Disposition:** Absorb reviewed conclusions into durable `analysis/`,
> `compiler/`, and exact cross-domain owners; retain bounded handoffs and
> decision rationale; delete this package before `docs-next/` authority
> cutover.

## Purpose

Stage 4A determines how zkc asks and answers exact semantic and cryptographic
questions over admitted Stage 3 subjects, and only then how a Protocol compiler
constructs, validates, constrains, compares, and selects among independently
admitted and exactly related alternatives.

This is one ordered co-design package:

```text
Stage 3 admitted subjects and checked structural relations
  -> Analysis questions, bases, derivations, and qualified judgments
  -> Compiler constraints and objectives over exact judgments
  -> total accounting over exact closed candidate and comparison domains
  -> checked complete-assessment or external-certificate sufficiency
  -> branchwise bounded decision

checked DecisionPolicy + any exact reached qualified subset
  + exact reached closure results actually read + audit-relative accounting
  -> independently checked explicitly open report
```

The report branch is independent of closed-domain and total-assessment
prerequisites; it makes only its exact subset/accounting claim.

Analysis meaning cannot be defined by Compiler policy, provider availability,
search behavior, or scores. Compiler is nevertheless an essential consumer
pressure: it must expose whether an Analysis result is too broad, too weak, or
missing an exact subject, assumption, map, outcome, or replay contract.

The package starts from the completed [Stage 4A entry
contract](../stage-3-protocol-and-relations/stage-4a-entry-contract.md) and the
durable Stage 3 target owners. Current semantic authority remains under
`docs/` until an explicit later cutover.

## Activation and completion result

Stage 4A is activated as a design-research branch. Activation authorizes only
the bounded research sequence in the [charter](charter.md). It does not select
an Analysis calculus, Compiler architecture, theorem system, proof assistant,
transform family, persistence format, implementation plan, or migration path.

The first bounded question tranche is:

```text
exact admitted Stage 3 subjects
  + observer-indexed equality, trace-equivalence, trace-refinement,
    and intentional-change questions
  + exact model/rule, assumptions, maps, read closure, and result schema
  -> Analysis-owned qualified judgment with independently checkable basis
```

This tranche must establish the common question/basis/derivation/result
discipline before distributional, soundness, knowledge, completeness,
`FSCompile`, property-transport, relation-satisfaction, or composition-property
families are selected. Those families are in whole-Stage scope and must be
instantiated before exit; they are not assumed to share more than the research
proves.

Compiler reconstruction and external research begin in parallel as consumer
and alternative probes. Compiler target selection waits for a provisional
Analysis model and must not redefine it.

Stage 4A subsequently completed the chartered reconstruction, comparative
research, equal-resolution candidate construction, thirty-nine integrated
scenarios, cross-cutting matrices, convergence, durable promotion, Stage 4B
peer reconciliation, absorption accounting, and exit audit. It selected
Candidate B's family-indexed Analysis and five-plane validated-decision
Compiler, with bounded mechanisms from Candidates A, C, D, and E. The
selection is a non-normative target architecture, not a property, compiler,
implementation, or migration result.

## Workstream closure

| Workstream | State | Required result |
|---|---|---|
| Activation and charter | Complete | Frozen intake, first tranche, sequence, scenarios, outputs, non-goals, reopening, and exit gate |
| Current Analysis reconstruction | Closed; audit passed | Normative, implementation, test, example, conflict, and unknown map |
| Current Compiler reconstruction | Closed; audit passed | Normative, implementation, test, example, conflict, and unknown map |
| Current history, authority, and consumers | Closed; audit passed | Evolution, assurance lanes, executable authority, consumers, persistence, and outcome compression |
| Joint current-model synthesis | Closed; audit passed | Preserved strengths, coupling, conflicts, Stage 3 pressure, and open axes |
| Native design forces and opportunities | Complete | zkc-specific requirements, capability opportunities, falsifiers, and non-goals |
| Primary-source cases | Complete | Analysis, cryptographic reasoning, compiler, and transformation-system dossiers with transfer limits |
| Equal-resolution candidates | Complete; audit passed | Five materially different integrated Analysis/Compiler architectures over common axes |
| Validation and scenarios | Complete; audit passed | Cross-cutting matrices, counterexamples, thirty-nine scenario outcomes, and peer-branch pressure |
| Convergence and promotion | Complete | Selected model, rejections, deferrals, reversal triggers, durable owner contracts, and gap map |
| Absorption and exit | Complete; CLEAN and CLOSED | Temporary-input accounting, documentation validation, and bounded exit |

Files are created when their work begins. Empty destination placeholders do not
count as progress.

## Package inventory

| Page | State | Role |
|---|---|---|
| This index | Complete | Package state, navigation, workstream closure, and deletion gate |
| [Charter](charter.md) | Satisfied | Frozen intake, ownership, sequence, work products, scenarios, non-goals, exit, and reopening contract |
| [Current Analysis](current-analysis.md), [current Compiler](current-compiler.md), [history/authority/consumers](current-history-authority-and-consumers.md), and [joint synthesis](current-model-synthesis.md) | Complete | Current normative, implementation, test, example, conflict, unknown, and consumer reconstruction |
| [Design forces and opportunities](design-forces-and-opportunities.md) | Complete | Native requirements, option-value opportunities, falsifiers, and non-goals |
| [Primary-source cases](cases/README.md) | Complete | Analysis/proof-system, ZK-theory, and compiler/transformation dossiers with transfer limits |
| [Equal-resolution candidates](candidate-models.md) | Complete and frozen | Five integrated architectures over the same Analysis and Compiler closure axes |
| [Integrated target](target-semantic-model.md) | Selected and frozen | Complete Candidate-B target with bounded A/C/D/E mechanisms; historical provisional header retained to preserve the audited hash |
| [Scenario results](scenario-results.md) and [validation matrices](validation-matrices.md) | Complete; audits passed | Thirty-nine pressure cases plus cross-cutting identity, authority, outcome, trust, capability, and extension closure |
| [Current-to-target gap](current-to-target-gap.md) | Complete | Retained, split, replaced, new, and deferred semantic correspondence without migration planning |
| [Stage 4B reconciliation](stage-4b-reconciliation.md) | CLEAN and CLOSED | Exact peer boundary, complete dormant relation-source intake, separately authorized selected-target cold handoff, and later-owned-input contract; Stage 4B remains unactivated |
| [Convergence](convergence.md) | Complete | Integrated selection, research basis, alternative dispositions, costs, capabilities, reversals, and promotion status |
| [Absorption record](absorption-record.md) and [exit audit](exit-audit.md) | Complete | Exact durable-destination, temporary-input, deletion-gate, snapshot, and documentation-exit accounting |

The target, candidate portfolio, scenario record, and validation matrices are
immutable historical pre-selection snapshots. Their headers and phase-local
status text may retain pending-review or pending-selection language;
[convergence](convergence.md) and the durable pages own the final selection
state. Preserving those snapshots protects the exact independently audited
hashes.

## Working rules

1. Write research and design artifacts in English.
2. Treat current specifications as authority and code/tests as correspondence,
   feasibility, and behavior evidence within their exact scope.
3. Preserve the frozen Stage 3 subject, identity, view, authority, qualified-
   outcome, replay, Fiat--Shamir, and composition boundaries unless a chartered
   reopening gate is met.
4. Complete Analysis meaning before Compiler consumes it, while allowing
   concrete Compiler read-set counterexamples to reopen only the affected
   Analysis envelope.
5. Compare preservation, alignment, structural-redesign, and capability-
   expanding candidates at equal resolution.
6. Use primary sources as design input, not as votes or imported authority.
7. Keep theorem truth, theorem correspondence, model adequacy, derivation
   checking, implementation evidence, and consumer reliance distinct.
8. Keep proposal, target admission, checked predecessor/successor relation,
   property transport, constraint satisfaction, scoring, and selection
   distinct.
9. Preserve affirmative, fact-retaining negative, unsupported, cannot-answer,
   refused, malformed, and checker-failure outcomes where applicable.
10. Do not implement or plan migration to make a candidate appear feasible.

## Next gate

Stage 4A is complete. No later stage starts automatically. Stage 4B may begin
only through an explicit activation decision using the frozen Stage 3 entry
contract and the closed [peer reconciliation](stage-4b-reconciliation.md).
Implementation, migration, normative consolidation, and authority cutover
remain separate later stages.
