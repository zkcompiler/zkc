# Protocol projects

The examples compose the maintained source libraries through ordinary Entries.
Start with Schnorr, then Sumcheck and FRI before the STARK examples.

| Project | What it shows |
|---|---|
| [Schnorr](schnorr/README.md) | A generic group protocol, interactive execution and independent proofs; a [Spongefish variant](schnorr/spongefish/README.md) selects an external transcript and byte format |
| [Sumcheck](sumcheck/README.md) | Public-table multilinear Sumcheck, [composition](sumcheck/composed/README.md), and a [product expression](sumcheck/product/README.md) with extension-field challenges |
| [FRI](fri/README.md) | Authenticated folding and a bounded terminal polynomial |
| [Fibonacci](fibonacci/README.md) | One STARK protocol applied to Clean and Plonky3 AIRs |
| [FemtoCairo](femtocairo/README.md) | Clean VM execution with program and immutable-memory lookups |
| [Bulletproofs+](bulletproofs-plus/README.md) | Monero range proofs with reusable weighted inner-product rounds, exact external bytes and managed randomness |

Each project owns its concrete domains, Entries and invocation inputs. Reusable
algorithms live in [`libraries/`](../../libraries/README.md). Language feature
clients and compiler edge cases live under `common/tests/fixtures/projects/`.

With built tools on `PATH`, run `zkc check` inside a project, then `zkc prove`
and `zkc verify`. `zkc run` selects an interactive Entry when one is declared.
`zkc prepare` creates missing input templates and preserves existing values.
See the [walkthrough](../../docs/getting-started.md) and
[Entry guide](../../docs/runtime/entries.md) for selection and input paths.
