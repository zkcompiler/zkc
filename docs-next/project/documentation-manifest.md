# Documentation manifest

> **Document kind:** Manifest
> **Document state:** Scaffold
> **Provisional owner:** `project`
> **Authority:** This is the single inventory for `docs-next/` only. It does
> not alter the authority map under [`docs/`](../../docs/README.md).

## Manifest rule

Every durable page in `docs-next/` must appear here exactly once. Reader maps
may group or recommend pages, but they must not maintain a second exhaustive
authority list. A future check should validate this manifest against the tree
and validate all root and domain routes against it.

The page header is the source for kind, state, owner, and authority. The columns
below are a derived navigation catalog and must eventually be validated against
those headers rather than edited as independent metadata.

All entries currently have scaffold state and no authority outside the design
of this scaffold.

| Path | Kind | Provisional owner | Purpose |
|---|---|---|---|
| [`README.md`](../README.md) | Index | `project` | Root reader route, authority warning, and proposed domain map |
| [`project/README.md`](README.md) | Area index | `project` | Project boundary and local navigation |
| [`project/documentation-governance.md`](documentation-governance.md) | Governance proposal | `project` | Authority classes, page contracts, ownership, and writing rules |
| [`project/information-architecture.md`](information-architecture.md) | Architecture proposal | `project` | Domain criteria, dependencies, bridges, and split or merge rules |
| [`project/migration-policy.md`](migration-policy.md) | Governance proposal | `project` | Controlled migration and cutover process |
| [`project/documentation-manifest.md`](documentation-manifest.md) | Manifest | `project` | Single scaffold page inventory |
| [`foundation/README.md`](../foundation/README.md) | Domain index | `foundation` | Shared semantic substrate boundary |
| [`pir/README.md`](../pir/README.md) | Domain index | `pir` | Protocol semantic object and lifecycle boundary |
| [`relations/README.md`](../relations/README.md) | Domain index | `relations` | External relation and correspondence boundary |
| [`judgments/README.md`](../judgments/README.md) | Domain index | `judgments` | Post-seal property-analysis boundary |
| [`compiler/README.md`](../compiler/README.md) | Domain index | `compiler` | Checked protocol transformation and selection boundary |
| [`endpoints/README.md`](../endpoints/README.md) | Domain index | `endpoints` | Projection, OIR, and abstract endpoint behavior |
| [`realization/README.md`](../realization/README.md) | Domain index | `realization` | Supplier binding, emission, deployment, invocation, and runtime boundary |
| [`evidence/README.md`](../evidence/README.md) | Domain index | `evidence` | Evidence objects, provenance, and claim-scope boundary |
| [`guides/README.md`](../guides/README.md) | Area index | `guides` | Reader journeys and task-oriented material |

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
