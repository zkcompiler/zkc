# Protocol projects

| Project | Library and Entry | Execution |
|---|---|---|
| [Finite computations](finite-computations/README.md) | Shared domain, Local and Math libraries | Strict dot product, records and filters, bounded reads and nested matrix traversal |
| [Scoped computations](scoped-computations/README.md) | Generic user apply/forward functions and a module wrapper | Nested callbacks with record projections, vector lookup and capture-selected ownership |
| [Schnorr](schnorr/README.md) | Generic group protocol, discrete-log relation and concrete Entry | Interactive exchange or independent transcript-derived proofs |
| [Constructed Schnorr](constructed-schnorr/README.md) | Generic Schnorr with an application-selected provider and record codec | Raw external proofs through programmable construction |
| [Spongefish Schnorr](spongefish-schnorr/README.md) | Explicit source transcript with BLS12-381 G1 byte encodings | Raw 80-byte external proofs with ordinary prover/verifier execution |
| [Sumcheck](sumcheck/README.md) | Generic public-table protocol and bounded-round Entry | Actual receives, repeated state and direct terminal evaluation |
| [Composed Sumcheck](composed-sumcheck/README.md) | Two reductions composed with separate terminal checks | Reusable role-local evaluation obligations |
| [Expression Sumcheck](expression-sumcheck/README.md) | Generic Sumcheck over a captured ring asset with KoalaBear/Ext8 Entries | Exact round coefficients, extension-field challenges and public-table terminal evaluation |
| [AIR STARK](air-stark/README.md) | Captured Plonky3 AIR with quotient, DEEP and FRI libraries | Separate prover/verifier Hosts over base-field trace commitments and extension-field claims |
| [Accumulator machine](accumulator-machine/README.md) | External CPU/program/memory relation with LogUp or grand-product reductions | Whole-Bundle proof through phased auxiliary commitments, OOD/DEEP and shared FRI |
| [Mathematics](mathematics/README.md) | Formal polynomial and runtime vector helpers | Formal evaluation compared with a shared affine fold |
| [Mathematical notation](mathematical-notation/README.md) | Named and library-defined vector calls with Unicode source names | Weighted interpolation and Hadamard multiplication through the common Host |
| [Finite reductions](finite-reductions/README.md) | Library-owned sums and products over strict zipped field vectors | Named and symbolic reductions with scalar captures and optional checked dot fusion |
| [Native map](native-map/README.md) | Row formulas applied to whole KoalaBear/Ext8 columns with checked `map` | A gate check over public columns and an interactive challenge combination |
| [Polynomial opening](polynomial-opening/README.md) | Common opening equations composed with row commitments and FRI | Independent nonhiding evaluation proof with explicit final discharge |
| [FRI](fri/README.md) | Generic binary FRI with authenticated rows | Commitments, extension-field folding challenges, simultaneous queries and a bounded terminal polynomial |
| [FRI fold](fri-fold/README.md) | Total arithmetic for batches of paired evaluations | Forwarded projections, intermediate collection lengths and next-layer residuals |
| [LogUp rows](logup-rows/README.md) | Tuple compression and reciprocal equations | Ordered inner folds, collection lengths and fixed compression weights |
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
