# Documentation manifest

> **Document kind:** Manifest
> **Document state:** Active transition manifest
> **Provisional owner:** `project`
> **Authority:** This is the single inventory for `docs-next/` only. It does
> not alter the authority map under [`docs/`](../../docs/README.md).

## Manifest rule

Every durable page in `docs-next/` must appear here exactly once. Reader maps
may group or recommend pages, but they must not maintain a second exhaustive
authority list. A future check should validate this manifest against the tree
and validate all root and domain routes against it.

There is one temporary exception. [`notes/README.md`](../notes/README.md) is a
durable workspace boundary and therefore appears in this manifest. The
disposable working notes it inventories do not. They must appear exactly once
through the hierarchical inventory rooted there: the root inventories direct
packages or standalone notes, and each package README inventories its direct
children. They may not be durable dependencies and must all be absorbed or
rejected before the directory is deleted at cutover.

The page header is the source for kind, state, owner, and authority. The columns
below are a derived navigation catalog and must eventually be validated against
those headers rather than edited as independent metadata.

Entries may record selected non-normative target decisions, but none has
authority over the current corpus under `docs/` before explicit cutover.

| Path | Kind | Provisional owner | Purpose |
|---|---|---|---|
| [`README.md`](../README.md) | Index | `project` | Root reader route, authority warning, and proposed domain map |
| [`project/README.md`](README.md) | Area index | `project` | Project boundary and local navigation |
| [`project/v0-semantic-architecture.md`](v0-semantic-architecture.md) | Architecture proposal | `project` | Reconstructed current model, integrated selected Stage 1--4A backbone, later redesign surfaces, and work sequence |
| [`project/protocol-ir-architecture.md`](protocol-ir-architecture.md) | Architecture decision | `project` | Selected non-normative Stage 1 semantic subjects, identity algebra, canonical PIR boundary, carrier role, and transition-research entry contract |
| [`project/transition-and-bridge-architecture.md`](transition-and-bridge-architecture.md) | Architecture decision | `project` | Selected non-normative Stage 2 transition invariants, lifecycle, checker placement, bridge ownership, outcomes, and Stage 3 entry boundary |
| [`project/protocol-and-relations-architecture.md`](protocol-and-relations-architecture.md) | Architecture decision | `project` | Selected non-normative Stage 3 operational Protocol, canonical carrier, typed satellites, Relations, Fiat--Shamir, and composition architecture |
| [`project/analysis-and-compiler-architecture.md`](analysis-and-compiler-architecture.md) | Architecture decision | `project` | Selected non-normative Stage 4A federated Analysis and validated-decision Compiler architecture |
| [`project/v0-design-program.md`](v0-design-program.md) | Design-research execution plan | `project` | Single semantic redesign sequence, dependency stages, convergence, and cutover preparation |
| [`project/design-research-method.md`](design-research-method.md) | Governance and research-method proposal | `project` | Common research lenses, package cycle, candidate portfolio, evaluation axes, and gates |
| [`project/documentation-governance.md`](documentation-governance.md) | Governance proposal | `project` | Authority classes, page contracts, ownership, and writing rules |
| [`project/information-architecture.md`](information-architecture.md) | Architecture map | `project` | Domain criteria, dependencies, bridges, and split or merge rules |
| [`project/migration-policy.md`](migration-policy.md) | Governance proposal | `project` | Controlled migration and cutover process |
| [`project/documentation-manifest.md`](documentation-manifest.md) | Manifest | `project` | Single scaffold page inventory |
| [`foundation/README.md`](../foundation/README.md) | Domain index | `foundation` | Shared semantic substrate boundary |
| [`foundation/executable-foundations.md`](../foundation/executable-foundations.md) | Target semantic specification | `foundation` | Fixed bootstrap, typed identities and regimes, domain-indexed values, portable semantic functions, typed completed failures, deterministic evaluation control, and operational noncompletion boundaries |
| [`pir/README.md`](../pir/README.md) | Domain index | `pir` | Protocol semantic object and lifecycle boundary |
| [`pir/protocol-lifecycle.md`](../pir/protocol-lifecycle.md) | Architecture proposal | `pir` | Superseded first Stage 1 baseline for Protocol root, identity, carrier, authority graph, admission, and lifecycle |
| [`pir/protocol-model.md`](../pir/protocol-model.md) | Target semantic specification | `pir` | Candidate finite operational InteractiveCore and Protocol model, identity, execution, admission, outcomes, and views |
| [`pir/canonical-pir.md`](../pir/canonical-pir.md) | Target semantic specification | `pir` | One-root canonical MLIR PIR profile, semantic bijection, authentication, admission, information-loss, persistence, and replay contract |
| [`pir/interfaces-and-plans.md`](../pir/interfaces-and-plans.md) | Target semantic specification | `pir` | Independently identified Protocol Interface and Prover Plan subjects, codecs, admission, PlanRealizes, and downstream exports |
| [`pir/fiat-shamir-and-composition.md`](../pir/fiat-shamir-and-composition.md) | Target semantic specification | `pir` | Transcript construction, Fresh-to-Fiat--Shamir structural construction, semantic Core composition, checked maps, outcomes, and replay |
| [`relations/README.md`](../relations/README.md) | Domain index | `relations` | External relation and correspondence boundary |
| [`relations/relation-model.md`](../relations/relation-model.md) | Target semantic specification | `relations` | Relation definition, interface, instance, witness, binding, artifact ingress, comparison, grounding, and satisfaction boundary |
| [`relations/protocol-correspondence.md`](../relations/protocol-correspondence.md) | Target semantic specification | `relations` | Exact Protocol-at-Interface and instance correspondence questions, checked outcomes, capabilities, read closure, and replay |
| [`analysis/README.md`](../analysis/README.md) | Domain index | `analysis` | Post-admission property-analysis boundary and typed judgment outputs |
| [`analysis/analysis-model.md`](../analysis/analysis-model.md) | Target semantic specification | `analysis` | Family-indexed Analysis lifecycle, identity, basis, support, validation, qualified outcomes, authority, and trust |
| [`analysis/semantic-relations.md`](../analysis/semantic-relations.md) | Target semantic specification | `analysis` | Core/Protocol equality, traces, refinement, intentional change, distribution, cost, and relation-satisfaction seam |
| [`analysis/cryptographic-properties.md`](../analysis/cryptographic-properties.md) | Target semantic specification | `analysis` | Completeness, soundness, knowledge, zero-knowledge, quantitative models, and Fiat--Shamir applicability |
| [`analysis/transport-composition-and-replay.md`](../analysis/transport-composition-and-replay.md) | Target semantic specification | `analysis` | Property transport, composition, coverage, replay, persistence, caching, trust, and extension |
| [`compiler/README.md`](../compiler/README.md) | Domain index | `compiler` | Unauthoritative proposal orchestration and validated-decision selection boundary over independently admitted, owner-qualified transitions |
| [`compiler/compiler-model.md`](../compiler/compiler-model.md) | Target semantic architecture | `compiler` | Five-plane validated-decision Compiler, problem/policy/run identities, authority, and outcomes |
| [`compiler/proposals-relations-and-domains.md`](../compiler/proposals-relations-and-domains.md) | Target semantic specification | `compiler` | Search, frozen proposal scope, per-alternative target admission and transitions, total resolution, legality, candidates, and domain closure |
| [`compiler/assessment-selection-and-replay.md`](../compiler/assessment-selection-and-replay.md) | Target semantic specification | `compiler` | Qualification resolution, comparison domains, assessment inputs, objectives, decisions, reports, replay, and peer boundaries |
| [`oir/README.md`](../oir/README.md) | Domain index | `oir` | OIR projection, identity, and abstract endpoint behavior |
| [`realization/README.md`](../realization/README.md) | Domain index | `realization` | Supplier binding, emission, deployment, invocation, and runtime boundary |
| [`evidence/README.md`](../evidence/README.md) | Domain index | `evidence` | Evidence objects, provenance, and claim-scope boundary |
| [`guides/README.md`](../guides/README.md) | Area index | `guides` | Reader journeys and task-oriented material |
| [`notes/README.md`](../notes/README.md) | Temporary workspace index | `project` | No-authority inventory, absorption rules, and deletion gates for design incubation |

## Future manifest fields

Before content migration, the manifest should become machine-checkable and add:

- stable page identifier;
- exact document state and authority class;
- owning domain;
- normative subjects, where applicable;
- upstream dependencies;
- supersedes and superseded-by links; and
- current-source provenance during migration.

Those fields should be added when a validator consumes them. Until then, this
human-readable table avoids inventing an unimplemented metadata format.
