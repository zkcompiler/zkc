# Schnorr

`Schnorr<G>` is a three-message proof-of-discrete-log interaction over an
installed group. The prover draws a nonce, sends its commitment, receives the
verifier's challenge and sends a response. The verifier checks the equation
using the received commitment and response. `DLog` records the mathematical
statement/witness relation; it adds no implicit protocol guard.

This package uses the installed prelude and has no source package dependencies.
Applications choose the group, transcript construction, Entries and input policy.
The [example](../../../../examples/projects/schnorr/README.md) selects BLS12-381 G1
and Merlin; its [Spongefish variant](../../../../examples/projects/schnorr/spongefish/README.md)
selects a concrete byte transcript. [Sigma compositions](../compositions/README.md)
share a challenge across statements.

Check this package through its `zkc.toml`. Positive executions and false-statement
controls exercise both interactive and independent proof paths. They establish
bounded execution evidence, not knowledge soundness, zero knowledge or native
Lean correspondence.
