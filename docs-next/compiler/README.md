# Protocol compiler

> **Document kind:** Domain index
> **Document state:** Active target-domain index
> **Target alignment:** Selected Stage 4A validated-decision Compiler target
> **Provisional owner:** `compiler`
> **Authority:** None during the transition. Current compiler semantics remain
> governed by the [Compiler Core specification](../../docs/spec/compiler.md).
> **Closure interpretation:** This index records a selected package-resolution
> target. `Selected`, `target`, and `exact` describe intended role, scope, and
> ownership; they do not assert integrated definition closure or semantic
> freeze. The [v0 Semantic Design Program](../project/v0-design-program.md#14-progress-and-change-control)
> owns the live gate.

## Purpose

`compiler/` owns proposal orchestration and deterministic selection over exact,
already admitted Protocol alternatives together with exact qualified
predecessor/successor relation results: finite comparison domains,
transformation requests, constraints, objectives, comparison, and decision
recomputation. It does not admit an alternative, erase a relation result's
qualified outcome, or make a source/target relation true by selecting it.

This is the protocol compiler, not a name for the entire zkc pipeline.

## Owns

- exact admitted Protocol and typed-result ingress;
- exact frozen proposal scopes, semantic candidate domains, derived qualified
  comparison domains, and their independently checked closure;
- transform-family proposals, applications, plans, lineage, and candidate
  production;
- orchestration of PIR-owned target authentication and admission, followed by
  relation-specific predecessor/successor checking;
- exact per-result relation checkers for transform families explicitly housed
  beneath Compiler, while other relation owners remain independently cited;
- compiler-local request legality and explicit consumption of exact qualified
  checked Protocol relations;
- use of exact Analysis judgments, including their subject, question,
  assumptions, qualified outcome, complete `ExactJudgmentBinding`, complete
  `ExactCheckedResultAuthorityBinding<Analysis,F>`, assurance/trust, matching inert
  `OwnerCapabilityRequirement`,
  authenticated immediate owner-policy disposition, and complete transitive
  source-operation-policy dependency closure, in constraints and objectives;
- objective values, comparison, scoring, and deterministic selection;
- complete declared comparison domains, successful `NoEligible`, compiler
  requests, plans, proposals, results, and decision checking; and
- provider-specific protocol transformations as separate profiles beneath the
  generic compiler contract.

The term “transform realization” must remain distinct from downstream target
realization. Compiler realization constructs an unauthoritative canonical
successor proposal; target realization implements an already fixed endpoint.

## Does not own

- relation compilation or relation satisfaction;
- PIR structure, authentication or admission authority, or artifact identity;
- successor authentication or admission;
- a source/target relation merely because the compiler proposed, scored, or
  selected a target;
- `FSCompile` or another Analysis-owned semantic judgment;
- the meaning or truth of property judgments it consumes;
- `PropertyTransport`, even when a compiler constraint requests a transported
  property;
- PIR-to-OIR projection;
- backend lowering, code generation, deployment, or invocation;
- compiler UI and command-line behavior as semantic definitions; or
- test outcomes and performance measurements.

A provider may internally reopen an admitted clone as unauthoritative Open PIR,
but its output is only a proposal. PIR authenticates and admits the target;
then the exact transform-family bridge checks the predecessor/successor
relation. Its `ProtocolId` is recomputed: the empty identity plan may reproduce
the source Protocol and ID, while a content-changing plan produces a different
subject. Target admission alone proves no preservation or refinement.

## Dependencies

- `foundation/` for exact authorities, identity, and immutable capabilities;
- `pir/` for input and output protocol semantics;
- `analysis/` for typed properties, derivations, and result interpretation;
- `relations/` for explicit prerequisites that transformations may preserve or
  require; and
- conditionally, `evidence/` for exact `EvidenceQualifiedEstimate`, attributable
  record, and appraisal schemas named by an explicit decision policy.

Evidence is never part of candidate identity. It may enter assessment and
selection only when the exact policy declares it. Ambient measurements,
appraisals, or backend state cannot silently qualify, reject, rank, or select
a candidate.

The compiler must not depend on OIR projection for ordinary protocol selection.
Endpoint feasibility can enter only through an explicit independently owned
constraint over an exact named OIR or Realization result. Absence of that result
is not hidden candidate rejection, and backend ambient state is never a
substitute.

## Consumers and outputs

- PIR owns successor authentication and whole-Protocol admission predicates;
- exact transform-family bridge owners, including profiles housed beneath
  Compiler, supply qualified A/N checked relations over exact admitted
  predecessors and successors;
- `analysis/` owns any `PropertyTransport` derivation and result consumed by a
  compiler constraint;
- `oir/` may project any resulting admitted Protocol;
- evidence records decision parity, provider behavior, and performance at
  exact scope; and
- guides expose author and operator workflows.

## Bridge ownership

`compiler/` owns how admitted Protocols, exact qualified checked Protocol
relations, and exact Analysis results become candidate constraints, objectives,
complete comparison domains, and selection decisions. It does not own the
upstream meaning or truth of any input. Every use preserves its complete owner
created exact source-authority binding, matching inert
`OwnerCapabilityRequirement`, authenticated immediate policy disposition, and
transitive source-policy closure; the exact
Compiler policy and every bound owner policy must permit the named consumer and
purpose.

The Compiler path preserves five authority planes. They are ownership
partitions, not a temporal pipeline: per-alternative PIR admission and exact
transition qualification occur after scope freezing and before the total
alternative ledger is finalized. The detailed execution order is fixed by the
[Compiler model](compiler-model.md).

```text
problem: TransformProblem + DecisionPolicy
production: replaceable unauthoritative search and proposals
proposal resolution: frozen ProposalScope + declared alternatives
  + later total alternative ledger
qualification/assessment: PIR admission + exact relations + exact inputs
decision:
  closed path: closed candidate/comparison domains + total accounting
    -> checked sufficiency + branchwise bounded decision
  independent report side exit: checked DecisionPolicy
    + any exact reached qualified subset
    + exact reached closure results actually read + audit accounting
    -> independently checked open report
global outer outcome, not an additional plane:
  preparation/check failure at any reached operation -> outer outcome
```

The report path is a side exit, not a weakened decision path: it requires
neither closed `D`/`Q` nor total qualification or assessment accounting.

The provider's mutable clone has no inherited authority. A transform-family
checker establishes only its named qualified relation; the generic selection
engine does not infer or widen that result. A positive eligibility constraint
requires the exact affirmative capability. A fact-retaining negative may serve
only an explicitly negative constraint, while `Unsupported`, `CannotAnswer`,
`Refused`, `Malformed`, and `CheckerFailure` satisfy neither. Selection chooses
only a target that was already admitted and satisfies every declared positive
eligibility premise; it creates no Protocol and proves optimality only over the
declared complete domain. Relation adjacency or a preservation annotation
cannot produce a target property judgment: `PropertyTransport` remains
Analysis-owned.

Compiler decisions are likewise qualified. `NoEligibleCandidateIn<D,Q>` over
exact closed semantic and comparison domains is a successful bounded result,
not an unsupported transform,
missing basis, refusal, malformed request, checker failure, or incomplete
search. In the fully portable lane, an inert result may be persisted only for a
named independent consumer under an exact replay contract and conjunctive
source-policy permission; persistence never preserves authority. A result whose
own preimage names a local handle is nonpersistable and has no exact cold replay.

## Target documents

- [Selected Analysis and Compiler Architecture](../project/analysis-and-compiler-architecture.md)
- [Validated-decision Compiler Model](compiler-model.md)
- [Proposals, Transitions, and Candidate Domains](proposals-relations-and-domains.md)
- [Assessment, Selection, and Replay](assessment-selection-and-replay.md)

These pages are durable non-normative Stage 4A candidate targets at package
resolution. The current Compiler Core specification under `docs/` remains
authoritative until explicit normative consolidation and cutover.

## Reopened dependency boundary and later work

Stage 4A selected problem, policy, operational search, frozen proposal scope,
per-alternative target admission and transition qualification, total
alternative resolution, problem-local legality, candidate and comparison
domains, assessment inputs, typed constraints/objectives, decisions, open
reports, replay, trust, and Stage 4B/Evidence firewalls at its then-current
package resolution. The five-plane separation remains a candidate, not a
validated integrated Compiler contract. Its closure is downstream of frozen
PIR, Relations, and Analysis inputs and must be rechecked against those exact
subjects and results. Later work includes concrete transform families,
producer algorithms, checkers, certificate formats, objective profiles, wire
encodings, storage policies, and implementation organization.

Stage 4B may export exact endpoint-owned facts under the selected association
contract but remains unactivated. Stage 5 tests the joined capability surface.
Stages 7 and 8 retain normative consolidation, implementation architecture,
conformance, and migration.
