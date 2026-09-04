# OIR Semantic Profiles

> **Document kind:** Publication routing index
> **Document state:** Active non-normative target
> **Provisional owner:** `oir`
> **Authority:** None during transition. Current normative endpoint semantics
> remain under [`docs/`](../../../docs/README.md).

This directory contains the two strict owner-source manifests published by
OIR:

| Profile | Manifest | Semantic owner |
|---|---|---|
| Endpoint graph | [`endpoint-graph.json`](endpoint-graph.json) | [`projection-contract.md`](../projection-contract.md) |
| Projection relation | [`projection-relation.json`](projection-relation.json) | [`projection-contract.md`](../projection-contract.md) |

The endpoint graph is source-independent and imports no PIR profile. The
projection relation imports the PIR endpoint source-view profile and the OIR
endpoint graph. This direction prevents source-specific extraction from
becoming part of standalone endpoint meaning.

Foundation owns the reusable [publication mechanism](../../foundation/semantic-profile-publication.md),
the complete [manifest index](../../foundation/semantic-profile-manifests.json),
and independent reconstruction of the derived identity table.
These artifacts establish deterministic profile reconstruction only; they do
not establish local OIR validity, projection correctness, execution, or
implementation support.
