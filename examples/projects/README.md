# Protocol projects

| Project | Library and Entry | Execution |
|---|---|---|
| [Schnorr](schnorr/README.md) | Generic group protocol, discrete-log relation and concrete Entry | Interactive exchange or independent transcript-derived proofs |
| [Sumcheck](sumcheck/README.md) | Generic public-table protocol and bounded-round Entry | Actual receives, repeated state and direct terminal evaluation |
| [Expression Sumcheck](expression-sumcheck/README.md) | Generic Sumcheck over a captured ring asset with KoalaBear/Ext8 Entries | Exact round coefficients, extension-field challenges and public-table terminal evaluation |
| [AIR STARK](air-stark/README.md) | Captured Plonky3 AIR with quotient, DEEP and FRI libraries | Separate prover/verifier Hosts over base-field trace commitments and extension-field claims |
| [Accumulator machine](accumulator-machine/README.md) | External CPU/program/memory relation with LogUp or grand-product reductions | Whole-Bundle proof through phased auxiliary commitments, OOD/DEEP and shared FRI |
| [Mathematics](mathematics/README.md) | Formal polynomial and runtime vector helpers | Formal evaluation compared with a shared affine fold |
| [Mathematical notation](mathematical-notation/README.md) | Named and library-defined vector calls with Unicode source names | Weighted interpolation and Hadamard multiplication through the common Host |
| [Native map](native-map/README.md) | Row formulas applied to whole KoalaBear/Ext8 columns with checked `map` | A gate check over public columns and an interactive challenge combination |
| [FRI](fri/README.md) | Generic binary FRI with authenticated rows | Commitments, extension-field folding challenges, simultaneous queries and a bounded terminal polynomial |
| [Imported AIR](imported-air/README.md) | Captured Plonky3 AIR expression and relation Bundle | Actual trace checks and a disclosed-trace proof, plus coefficient and Ext8 point views |

The [walkthrough](../../docs/getting-started.md) runs the Schnorr project. Each project has an explicit `zkc.toml` source and asset map. Run
`zkc check --project=examples/projects/NAME/zkc.toml --declarations`, then
select an Entry by positional name for `inspect`, `run`, `prove` or `verify`.
The [common Host](../../docs/runtime/entries.md) compiles source in memory or
accepts an explicitly pinned package. `prepare` creates missing templates
under `inputs/<qualified.name>/`; existing values are preserved. Source execution
uses these paths by default, with explicit overrides available. These projects require no
protocol-specific executor. The [source project checks](../../common/tests/protocol/test_source_projects.py)
exercise their commands and invalid inputs/proofs.

Reusable protocol definitions live in [`libraries/`](../../libraries/README.md).
Each project owns its concrete domains, Entries and invocation inputs. Keep assets
used by only one project alongside that project; shared relation-ingress samples
live in [`relations/`](../relations/README.md). Assets and input maps an adapter
derives stay beside the export it checks them against.
