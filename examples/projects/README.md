# Protocol projects

| Project | Library and Entry | Execution |
|---|---|---|
| [Schnorr](schnorr/README.md) | Generic group protocol, discrete-log relation and concrete Entry | Interactive exchange or independent transcript-derived proofs |
| [Sumcheck](sumcheck/README.md) | Generic public-table protocol and bounded-round Entry | Actual receives, repeated state and direct terminal evaluation |
| [Expression Sumcheck](expression-sumcheck/README.md) | Generic Sumcheck over a captured ring asset with KoalaBear/Ext8 Entries | Exact round coefficients, extension-field challenges and public-table terminal evaluation |
| [Imported AIR](imported-air/README.md) | Captured Plonky3 AIR expression and relation Bundle | Actual trace checks and a disclosed-trace proof, plus coefficient and Ext8 point views |

The [walkthrough](../../docs/getting-started.md) runs the Schnorr project. Compile
explicit `--module=NAME=FILE` mappings, then invoke the selected package through
the [common Host](../../docs/runtime/entries.md). These projects require no
protocol-specific executor. The [source project checks](../../tests/protocol/test_source_projects.py)
exercise their commands and invalid inputs/proofs.

Reusable protocol definitions live in [`libraries/`](../../libraries/README.md).
Each project owns its concrete domains, Entries and invocation inputs. Keep assets
used by only one project alongside that project; shared relation-ingress samples
live in [`relations/`](../relations/README.md). Assets and requests an adapter
derives stay beside the export it checks them against.
