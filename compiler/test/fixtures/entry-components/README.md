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
required sealing metadata. Regenerate both pairs after building the affected
compiler tests:

```sh
build/compiler/test/zkc-language_entry_components_interface-test compiler/test/fixtures/entry-components
```

The generator first checks source correspondence, independent interface admission,
flat proof expansion, setup slices and generated Host families. The identical
originals deliberately have different authenticated job policies. A consumer
checks the original digest over the exact bytes; the toolchain digest describes
the producing build and is not a substitute for native/source authentication.
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
| `ordinary.mlir` | `2e2b8cc036f4670d79177e0a3c60e97a4fd900f54fd27d846a19ea651be271a9` |
| `ordinary.json` | `67f7a869c27c763069d48d285c015c37a4916c9b11737b7ffbc47a033367da72` |
| `ordinary-run.mlir` | `2e2b8cc036f4670d79177e0a3c60e97a4fd900f54fd27d846a19ea651be271a9` |
| `ordinary-run.json` | `64489b9507522dd81bf08a2f42d5286cd2c470c8ed09b816e86ee9cdb0a33501` |
