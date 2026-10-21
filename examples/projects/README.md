# Protocol projects

The examples compose the maintained source libraries through ordinary Entries.
Start with Schnorr, then Sumcheck and FRI before the STARK examples.

| Project | What it shows |
|---|---|
| [Schnorr](schnorr/README.md) | A generic group protocol, interactive execution and independent proofs; a [Spongefish variant](schnorr/spongefish/README.md) selects an external transcript and byte format |
| [Sigma compositions](sigma/README.md) | Schnorr AND with a shared challenge and Chaum–Pedersen with a shared witness, interactive and noninteractive |
| [Sumcheck](sumcheck/README.md) | Public-table multilinear Sumcheck, [composition](sumcheck/composed/README.md), and a [product expression](sumcheck/product/README.md) with extension-field challenges |
| [GKR](gkr/README.md) | Layered arithmetic circuits with public wiring: degree-two Sumcheck per layer and the line reduction |
| [FRI](fri/README.md) | Authenticated folding and a bounded terminal polynomial |
| [Committed opening](committed-opening/README.md) | One Keccak row commitment, one index request on a hash-chain transcript and an authenticated terminal opening |
| [Fibonacci](fibonacci/README.md) | One STARK protocol applied to Clean and Plonky3 AIRs |
| [Parameterized STARK](stark/README.md) | The same AIRs through the configurable STARK library: quartic challenges, Poseidon2 Merkle trees, pruned multi-openings |
| [FemtoCairo](femtocairo/README.md) | Clean VM execution with program and immutable-memory lookups |
| [Bulletproofs+](bulletproofs-plus/README.md) | Monero range proofs with reusable weighted inner-product rounds, exact external bytes and managed randomness |
| [EIP-4844](eip4844/README.md) | Ethereum blob commitments and opening proofs, reproducing c-kzg-4844's challenge hash inputs, with a digest-pinned trusted setup input |

Each project owns its concrete domains, Entries and invocation inputs. Reusable
algorithms live in [`libraries/`](../../libraries/README.md). Language feature
clients and compiler edge cases live under `common/tests/fixtures/projects/`.

With built tools on `PATH`, run `zkc check` inside a project, then `zkc prove`
and `zkc verify`. `zkc run ProtocolName` uses a concrete protocol's default run;
`zkc run 'ProtocolName<Arguments>'` selects a closed generic specialization.
An `entry fn` can name that configuration or add application logic.
`zkc prepare` creates missing input templates and preserves existing values.
See the [walkthrough](../../docs/getting-started.md) and
[Entry guide](../../docs/runtime/entries.md) for selection and input paths.
