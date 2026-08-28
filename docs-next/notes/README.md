# Temporary design notes

> **Document kind:** Temporary workspace index
> **Document state:** Scaffold
> **Provisional owner:** `project`
> **Authority:** None. Pages under this directory are design-incubation
> material. They cannot define semantics, report current support, record a
> decision, or authorize implementation work.
> **Disposition:** Absorb reviewed conclusions into their durable owning pages,
> then delete this directory before `docs-next/` cutover.

## Purpose

`notes/` prevents redesign candidates, cautions, and unresolved questions from
being lost while the v0 model is reconstructed. It is intentionally temporary.
It may contain overlapping alternatives and repeated context that would be
unacceptable in the final documentation corpus.

The directory is not a semantic domain, document-kind destination, roadmap,
issue tracker, private review archive, or substitute for the existing
authoritative specifications. It exists only between initial reconstruction
and absorption into durable domain owners.

## Authority rule

When a note disagrees with another source, use this order:

1. the current owner under [`docs/`](../../docs/README.md);
2. a ratified future owner under `docs-next/`, once one exists;
3. an accepted decision reflected in the owning specification; and
4. this directory only as a reminder that a question or candidate exists.

Detail does not strengthen a note's authority. Code, tests, research papers,
and prior design material are evidence used to evaluate a candidate; they do
not ratify the candidate.

## Temporary note contract

Every note in this directory must state:

```text
scope
current baseline
candidate changes or questions
why the subject is being revisited
known risks and non-claims
required research, opportunity exploration, or falsification tests
intended durable destination
deletion trigger
```

A note must label statements as one of:

- **current:** reconstructed from the current owning specification;
- **target:** already selected by target architecture but not necessarily
  admitted or implemented;
- **alignment:** current owners or summaries need reconciliation around an
  already selected model;
- **candidate:** a proposed change that has not been decided;
- **opportunity:** a potentially valuable capability or preserved option whose
  prerequisites and costs have not yet been decided;
- **question:** unresolved and requiring research;
- **caution:** a failure mode or non-implication the final design must preserve;
  or
- **recheck:** a concrete observation that must be verified at its owning
  source immediately before any repair.

Do not use `admitted`, `implemented`, `verified`, or `complete` without naming
the exact subject and authority that owns the claim.

## Promotion and deletion workflow

For each candidate:

1. reconstruct the exact current owner and implementation correspondence;
2. expand the design space through capability questions, primary research,
   clean-room alternatives, and explicit future-option analysis;
3. compare a portfolio that includes preserving the current design, completing
   or aligning it, structural redesign, and capability-expanding design;
4. test viable candidates against scenarios, counterexamples, and reversal
   conditions;
5. record a decision when the conclusion is durable and non-obvious;
6. update the destination specification or architecture page;
7. update status or evidence only when their separate claims changed;
8. remove the absorbed section from the temporary note; and
9. delete the note when no unresolved material remains.

The durable package discipline is defined by the
[Design Research Method](../project/design-research-method.md). Passing current
tests or failing to find a boundary defect does not end exploration.

Absorption means the durable owner contains the complete reviewed conclusion,
not that it links back here. Final public pages must never depend on this
directory.

## Deletion gates

Delete the entire directory before cutover only when all of the following are
true:

- every candidate has a durable destination, explicit rejection rationale, or
  intentionally deferred roadmap entry;
- every accepted semantic change is reflected in its owning specification;
- every durable rationale that readers need has an accepted decision record;
- every remaining open item is represented in the global roadmap or an owning
  specification's explicit extension boundary;
- no durable document links to `notes/`;
- the temporary inventory below is empty; and
- shadow validation reports no orphaned content.

Deletion is expected and is not historical data loss. Git history preserves
the working record; the final documentation should preserve conclusions and
rationale, not the incubation layout.

## Working-note inventory

These pages are intentionally excluded from the durable documentation manifest.
This index owns the direct children of `notes/`. Each package README owns its
direct children recursively; ordinary cross-links do not create another
inventory owner. This hierarchy must give every temporary page exactly one
inventory-owning route before cutover.

| Note | Scope | Intended destinations |
|---|---|---|
| [Stage 1: Protocol IR Architecture Research](stage-1-ir/README.md) | Completed bounded package: native design forces, current correspondence, comparative IR and theory cases, equal-resolution candidates, scenario falsification, convergence, and current-to-target gap | Selected decision absorbed into `project/protocol-ir-architecture.md`; candidate Protocol/Relations schemas were later selected and promoted at Stage 3 package resolution |
| [Stage 2: Transition and Bridge Contract Research](stage-2-transitions/README.md) | Completed bounded package: current transition reconstruction, external cases, candidate frameworks, matrices, scenario falsification, convergence, gap map, and Stage 3 handoff | Selected decision absorbed into `project/transition-and-bridge-architecture.md` and durable domain boundaries; retained until later exact seam absorption |
| [Stage 3: Protocol, Canonical PIR, and Relations Co-design](stage-3-protocol-and-relations/README.md) | Completed bounded package: current reconstruction, primary-source research, five equal-resolution candidates, frozen package-selection snapshot, matrices, sixteen scenarios, independent audits, convergence, promotion, and handoffs | Selected result absorbed into `project/protocol-and-relations-architecture.md`, candidate target owners under `pir/` and `relations/` at package resolution, and separate unactivated Stage 4A/4B entry contracts; retained until downstream absorption and deletion gates |
| [Stage 4A: Analysis and Compiler Co-design](stage-4a-analysis-and-compiler/README.md) | Completed bounded package: current reconstruction, primary-source research, five equal-resolution candidates, frozen package-selection snapshot, thirty-nine scenarios, matrices, independent audits, convergence, promotion, gap map, and peer reconciliation | Selected result absorbed into `project/analysis-and-compiler-architecture.md`, candidate target owners under `analysis/` and `compiler/` at package resolution, the Relations satisfaction and Protocol-correspondence boundary, and candidate source-binding/outcome refinements in the four PIR semantic pages; Stage 4B remains unactivated |
| [Semantic Revalidation and Redesign Cycle](semantic-revalidation-and-redesign/README.md) | Active cycle: K0--K2 are bounded-complete after reclosure, and K3-A through bounded K3-E are complete at their finite scopes. K4/P02 protocol-portfolio pressure is next; K5 independent freeze remains pending. R2 remains an evidence track and `P01` is retained at T3 | Exact affected owners under `project/`, `foundation/`, `pir/`, `relations/`, `analysis/`, `compiler/`, and the bounded `oir/` seam; full OIR/Realization design remains inactive until separately authorized |
| [Redesign Candidates](redesign-candidates.md) | Complete catalog of proposed changes, alignment work, alternatives, and promotion gates | `project/`, `foundation/`, `relations/`, `pir/`, `analysis/`, `compiler/`, `oir/`, `realization/`, `evidence/` |
| [Research Questions and Design Cautions](research-questions-and-cautions.md) | Cross-cutting unknowns, non-implications, recheck ledger, and research discipline | Domain specifications, architecture, decisions, roadmap, and evidence policy |
| [MLIR Carrier Assessment](mlir-carrier-assessment.md) | Why MLIR should remain, its costs, architectural limits, and reconsideration triggers | `project/` architecture, protocol/PIR carrier specification, OIR carrier specification, future decision record |
| [Stage 2 Transition and Bridge Charter](stage-2-transition-and-bridge-charter.md) | Completed historical charter: transition question, fixed Stage 1 intake, contract schema, scenarios, outputs, and satisfied exit gate | Selected result is `project/transition-and-bridge-architecture.md`; Stage 3 later consumed the handoff and completed |

## What must not be stored here

- security findings or exploit instructions;
- private competitive or product strategy;
- task-by-task implementation logs;
- external-conversation drafts;
- raw test output or benchmark records;
- release decisions;
- personal notes; or
- material that belongs under `docs/private/` according to its rules.

This workspace is public-ready in language but not final in authority or
structure.
