# Analysis Semantic Profiles

> **Document kind:** Publication routing index
> **Document state:** Active non-normative target
> **Provisional owner:** `analysis`
> **Authority:** None during transition. Current normative property semantics
> remain under [`docs/`](../../../docs/README.md).

Analysis publishes one common kernel and two independent downstream branches:

```text
analysis-kernel
  +--> analysis-cryptographic-property
  |      +--> analysis-afk-transport
  |             +--> analysis-afk-theorem-source-validation
  |
  +--> analysis-incremental-composition
           +--> analysis-incremental-composition-source-validation
```

The six manifests in this directory own the exact supported kinds, marked
semantic source, direct declaration uses, body compilers, admission signatures,
and failure schemas. Source-validation children import their semantic parents;
parents never import validation children. A validation-only change therefore
cannot rotate theorem meaning, while a parent change intentionally rotates its
child.

The durable [publication boundary](../profile-publication.md) explains the
profile partition. Foundation owns the reusable [publication mechanism](../../foundation/semantic-profile-publication.md),
the complete [manifest index](../../foundation/semantic-profile-manifests.json),
and independent reconstruction of the derived identity table.
Publication fixes deterministic finite language identity only; it proves no
property, theorem truth, checker soundness, or implementation conformance.
