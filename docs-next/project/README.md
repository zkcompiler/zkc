# Project documentation

> **Document kind:** Area index
> **Document state:** Scaffold
> **Provisional owner:** `project`
> **Authority:** None during the transition. Current project, status, and
> planning authority remains under [`docs/`](../../docs/README.md).

## Purpose

`project/` owns the cross-domain view of zkc: why the project exists, where its
scope stops, how the domains fit together, which document answers each class
of question, what the checkout currently claims, and what sequence of public
work is intended.

It is a governance and synthesis area, not a technical-semantic domain.

## Owns

- the project charter, scope, and explicit non-claims;
- the global system and domain map;
- documentation authority and conflict-resolution rules;
- the single documentation manifest;
- the single public capability/status dashboard;
- the single public roadmap and dependency order;
- cross-domain architectural decisions whose rationale cannot be owned by one
  technical domain;
- the cross-domain ecosystem role and authority map; and
- global extension indexes.

## Does not own

- exact artifact schemas, judgments, identities, refusal rules, or algorithms;
- detailed evidence records or their observations;
- domain-local architecture or decisions;
- tutorials and command workflows;
- concrete integration guides and time-sensitive ecosystem surveys; and
- internal research notes, review logs, issue queues, or implementation plans.

A project overview may summarize a technical concept for orientation, but it
must link to the semantic owner and cannot create a second definition.

## Dependencies and consumers

Project documents depend on every domain for accurate summaries. Every reader
and domain depends on `project/` for routing, current-status scope, and global
sequencing. This is a documentation dependency, not a semantic dependency.

## Initial documents

- [Documentation Governance](documentation-governance.md)
- [Information Architecture](information-architecture.md)
- [Migration Policy](migration-policy.md)
- [Documentation Manifest](documentation-manifest.md)

Future durable documents may include a charter, system architecture, current
status, roadmap, and decision index. They will be created only when content is
migrated and their authority is ready to be reviewed.

## Open boundary questions

- Which decisions are genuinely cross-domain rather than better owned beside
  the affected specification?
- Should the global terminology index live here as navigation or under
  `foundation/` as semantic routing? The current hypothesis is that
  `foundation/` owns the index and domains own the definitions.
- How much evidence detail belongs in the global status page before it should
  become a link to a bounded record under `evidence/`?
