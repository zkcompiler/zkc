# Protocol projects

| Project | Library and Entry | Execution |
|---|---|---|
| [Schnorr](schnorr/README.md) | Generic group protocol, discrete-log relation and concrete Entry | Interactive exchange or independent transcript-derived proofs |
| [Sumcheck](sumcheck/README.md) | Generic public-table protocol and bounded-round Entry | Actual receives, repeated state and direct terminal evaluation |

The [walkthrough](../../docs/getting-started.md) runs the Schnorr project. Compile
explicit `--module=NAME=FILE` mappings, then invoke the selected package through
the [common Host](../../docs/language/entries.md). These projects require no
protocol-specific executor. The [source project checks](../../tests/protocol/test_source_projects.py)
exercise their commands and invalid inputs/proofs.

Reusable protocol definitions live in [`libraries/`](../../libraries/README.md).
Each project owns its concrete domains, Entries and invocation inputs. Keep assets
used by only one project alongside that project; shared relation-ingress samples
live in [`relations/`](../relations/README.md).
