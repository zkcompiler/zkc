# Ordinary Entry component fixture

`ordinary.zkc` is an authored layout source fixture for independent compiler and
Rust consumer tests. It retains one distributed input root, a shared ordinary
statement, a prover witness, and an explicit verifier unit. `Round` supplies the
joint Run operation; `Demo` supplies independent proof operations; `Produce` and
`Check` exercise generated Host families. The verifier compares the transmitted
witness with the statement. This is an admission/execution control, not a secrecy
or soundness claim for an application protocol.

The native ABI has original inputs 0 (statement, P and V) and 1 (witness, P).
Public metadata selects port 0 paths [0] and [2] at V; native proof public indices
are [0]. Empty supply is mandatory despite having no native coordinate. Native
outputs contain one verifier Boolean. Fresh emitted fixture hashes and exact
component associations are retained in `ordinary.json` (proof job) and
`ordinary-run.json` (joint job), paired with their exact `.mlir` originals. They
use the strict current schema, including role-qualified public selections and
required sealing metadata. `zkc-language_entry_components_interface-test` writes
both pairs when given this directory.
[The interface fixture script](../../../../scripts/regenerate-interface-fixtures.py)
runs it, together with the other compiler-produced interface fixtures, from a
named compiler build and recomputes the digest table below:

```sh
python3 scripts/regenerate-interface-fixtures.py build/compiler
```

The generator first checks source correspondence, independent interface admission,
flat proof expansion, setup slices and generated Host families. The identical
originals deliberately have different authenticated job policies. A consumer
checks the original digest over the exact bytes; the toolchain digest describes
the producing build and is not a substitute for native/source authentication.
A consumer testing schema structure takes the toolchain digest as a fixture
parameter, so a compiler edit that changes only that identity needs no
regeneration.
Fresh package execution uses this same source with `Round`, `Demo`, `Produce`
and `Check`, exercising Run, proof generation/verification and typed Host calls.

`setup.zkc` covers selected verifier/prover keys, a shared commitment and an
unrelated witness sibling. `setup-product.zkc` places an initialized key beside
an ordinary public sibling inside an ordinary product below the distributed
root. These are admission and association controls; they require an authorized
setup provider for execution.

`array.zkc` checks that a generated Run family expands a closed logical array
from its actual static arguments through source, native emission and independent
Host comparison.

`opaque.zkc` retains a sealed ordinary witness with a private field. Its home
constructs and reveals the value; generated Prove and Run calls carry the whole
typed witness. Verify consumes public data and a candidate without constructing
the prover witness. The external proof and SDK input routes still refuse private
construction. Native Host controls check source correspondence, independent SSA
readback, exact generated fields and split ancestor/zero-extent authority. The
Rust pairing fixture `crates/zkc/tests/fixtures/entry_components_opaque.zkc`
exercises the same calls through freshly compiled packages and the actual SDK.

## Current fixture SHA-256

These hashes cover the exact retained bytes from the generator above.

| File | SHA-256 |
|---|---|
| `ordinary.mlir` | `970b39a8bf643156712523c089c032c0b635fbbd3b5e1b14a827bd089096b795` |
| `ordinary.json` | `22a58d673c31087148d5c64fb76761cd039cf069070368a572f9ef9ba73ad811` |
| `ordinary-run.mlir` | `970b39a8bf643156712523c089c032c0b635fbbd3b5e1b14a827bd089096b795` |
| `ordinary-run.json` | `ad38e50375124a1a0c2174c61cc2061fd7c368b34bb0e2880da32d8ba3223961` |
