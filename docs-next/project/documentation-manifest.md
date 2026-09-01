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
| [`foundation/semantic-profile-publication.md`](../foundation/semantic-profile-publication.md) | Target semantic specification and source-corpus index | `foundation` | Owner-neutral indexed profile publication, backward-compatible source editions, exact direct-use reconstruction, and independent compiler agreement |
| [`pir/README.md`](../pir/README.md) | Domain index | `pir` | Protocol semantic object and lifecycle boundary |
| [`pir/protocol-lifecycle.md`](../pir/protocol-lifecycle.md) | Architecture proposal | `pir` | Superseded first Stage 1 baseline for Protocol root, identity, carrier, authority graph, admission, and lifecycle |
| [`pir/interactive-core.md`](../pir/interactive-core.md) | Target semantic specification | `pir` | Active K2 finite InteractiveCore, Protocol, binding, scope, claim/reduction, oracle, causal execution, public-coin, and replay definitions |
| [`pir/fiat-shamir.md`](../pir/fiat-shamir.md) | Target semantic specification | `pir` | Canonical-framed transcript construction, derived influence, exact prefix, namespace, retry, sampling failure, and same-Core Fresh/FS definitions |
| [`pir/duplex-sponge-fiat-shamir.md`](../pir/duplex-sponge-fiat-shamir.md) | Target semantic specification | `pir` | Sibling overwrite-duplex transcript construction with runtime instance initialization, construction-public salt, fixed codecs, exact transitions, family receipts, and same-Core Fresh/FS definitions |
| [`pir/profiles/README.md`](../pir/profiles/README.md) | Target semantic specification and publication index | `pir` | Complete owner-source manifests, exact profile compilation grammar, root closures, derived identity table, and independent reconstruction boundary for six frozen upstream plus two dependent PIR profiles |
| [`pir/oracle-commitment-construction.md`](../pir/oracle-commitment-construction.md) | Target semantic specification | `pir` | Checked exact logical-Oracle-to-commitment Core construction, deterministic elaboration, maps, advice, bounds, process-local authority, and inert run receipts |
| [`pir/commitment-opening-verification.md`](../pir/commitment-opening-verification.md) | Target semantic specification | `pir` | Verifier-side public setup, opening claims, evidence, exact Core use, replay, and distinct Merkle/KZG profile shapes |
| [`pir/protocol-model.md`](../pir/protocol-model.md) | Historical target snapshot | `pir` | Pre-K2 finite operational Core/Protocol snapshot retained for reconstruction and provenance |
| [`pir/canonical-pir.md`](../pir/canonical-pir.md) | Target semantic specification | `pir` | Factor-preserving canonical MLIR carrier for one exact InteractiveCore/Protocol pair, inverse reads, external dependency closure, authentication, admission, persistence, and satellite exclusion |
| [`pir/interfaces-and-plans.md`](../pir/interfaces-and-plans.md) | Target semantic specification | `pir` | Protocol Interface and Prover Plan subjects, total invocation and presentation maps, decision and accepted-terminal recipes, Plan-owned strategy/session and continuation authority, one-use witness handoff, PlanRealizes, and source-ID-free PlanWitnessSurface |
| [`pir/endpoint-projection-views.md`](../pir/endpoint-projection-views.md) | Target semantic specification | `pir` | Closed verifier, Plan-specialized prover, and continuation-prover purposes; total source-read disposition; provenance-free source quotients; site-qualified private-output contracts; adequacy; exact canonical bodies; and checked extraction |
| [`pir/fiat-shamir-and-composition.md`](../pir/fiat-shamir-and-composition.md) | Historical target snapshot | `pir` | Pre-K2 Fiat--Shamir snapshot and historical semantic Core-composition candidate retained for later composition closure |
| [`relations/README.md`](../relations/README.md) | Domain index | `relations` | External relation and correspondence boundary |
| [`relations/relation-model.md`](../relations/relation-model.md) | Target semantic specification | `relations` | Profiled relation subjects and four Interface roles, private assignments and satisfaction, split Protocol/Plan bindings, three value-bridge lanes, artifact facts, confidential Plan-witness grounding, and typed recurrence inputs |
| [`relations/protocol-correspondence.md`](../relations/protocol-correspondence.md) | Target semantic specification | `relations` | Closed correspondence-question algebra, owner-derived reads, public/private same-run joining, direct same-process witness handoff, finite one-step recurrence, qualified outcomes, and replay boundaries |
| [`relations/recursive-composition-grounding.md`](../relations/recursive-composition-grounding.md) | Target semantic specification | `relations` | Total recursion-facing instance coverage, exact digest paths, narrow owner-local checked-result sources, finite live-chain non-aliasing, portable re-admission separation, and the CycleFold same-step guardrail |
| [`relations/profiles/README.md`](../relations/profiles/README.md) | Target semantic publication index | `relations` | Strict Relations owner-source manifest, exact PIR imports, semantic/module catalog separation, and independently reconstructed identity |
| [`analysis/README.md`](../analysis/README.md) | Domain index | `analysis` | Post-admission property-analysis boundary and typed judgment outputs |
| [`analysis/analysis-model.md`](../analysis/analysis-model.md) | Target semantic specification | `analysis` | Foundation-aligned minimum source ingress, strategy/experiment, identity, hypothesis, basis, authority, and qualified-outcome kernel |
| [`analysis/semantic-relations.md`](../analysis/semantic-relations.md) | Target semantic specification | `analysis` | Exact relation-source ingress and relation-bound Schnorr special-soundness coordinates |
| [`analysis/cryptographic-properties.md`](../analysis/cryptographic-properties.md) | Target semantic specification | `analysis` | Selected Schnorr special-soundness and AFK adaptive classical-ROM knowledge-soundness profiles with typed quantitative semantics |
| [`analysis/transport-composition-and-replay.md`](../analysis/transport-composition-and-replay.md) | Target semantic specification | `analysis` | Separate theorem applicability, property transport, loss-ledger consumption, and replay contracts |
| [`analysis/incremental-composition.md`](../analysis/incremental-composition.md) | Target semantic specification | `analysis` | Closed finite incremental-composition families, exact Relations-result ingress, theorem application, distinct depth and model axes, derived carried obligations, and portable-continuation separation |
| [`analysis/profile-publication.md`](../analysis/profile-publication.md) | Target semantic specification | `analysis` | Six-profile ownership split, exact publication law programs, direct-import topology, and profile-local rotation boundary |
| [`analysis/profiles/README.md`](../analysis/profiles/README.md) | Target semantic publication index | `analysis` | Strict Analysis owner-source manifests, two independent profile branches, and independently reconstructed identities |
| [`compiler/README.md`](../compiler/README.md) | Domain index | `compiler` | Unauthoritative proposal orchestration and validated-decision selection boundary over independently admitted, owner-qualified transitions |
| [`compiler/compiler-model.md`](../compiler/compiler-model.md) | Target semantic architecture | `compiler` | Five-plane validated-decision Compiler, problem/policy/run identities, authority, and outcomes |
| [`compiler/proposals-relations-and-domains.md`](../compiler/proposals-relations-and-domains.md) | Target semantic specification | `compiler` | Search, frozen proposal scope, per-alternative target admission and transitions, total resolution, legality, candidates, and domain closure |
| [`compiler/assessment-selection-and-replay.md`](../compiler/assessment-selection-and-replay.md) | Target semantic specification | `compiler` | Qualification resolution, comparison domains, assessment inputs, objectives, decisions, reports, replay, and peer boundaries |
| [`oir/README.md`](../oir/README.md) | Domain index | `oir` | Bounded OIR semantic, projection, identity, and abstract endpoint boundary |
| [`oir/projection-contract.md`](../oir/projection-contract.md) | Target semantic specification | `oir` | Minimum target-semantic OIR body, local admission, exact graph/static-contract correspondence, verifier and prover purposes, terminal-indexed private-continuation contract, qualified outcomes, identity, bounded support, and runtime Realization deferral |
| [`oir/profiles/README.md`](../oir/profiles/README.md) | Target semantic publication index | `oir` | Import-free endpoint-graph and PIR-relative projection profile manifests, exact direct imports, and independently reconstructed identities |
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
