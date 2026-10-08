# Entry and native execution hosts

`zkc` compiles `.zkc` Entry packages through the mathematical compiler and executes
the resulting `zkc.program/1` with the generic runtime. The public library has
three owners:

| Owner | Responsibility |
|---|---|
| `entry` | Authenticated packages, named input binding, compilation, execution and generated Rust data bindings |
| `run` | Authenticated run bundles, role preparation, scheduling, transport and bounded reports |
| `proof` | Independently admitted producer/verifier deployments, public binding, proof execution, attempts and setup authority |

`proof` also exports bounded proof readers/writers and execution reports.
Private `host` helpers own byte ingress, native input admission, immutable prover
material, operational capacities, setup validation and bounded compiler-process
execution. No host dispatches on a protocol name.

Use `zkc --help` or `zkc COMMAND --help`. The installed commands are:

- `compile`, `run-entry`, `prove`, `verify`, `bindings`.
- `run-bundle`.
- `produce-native-proof`, `validate-native-proof`.

An expected SHA-256 comes from trusted compilation or deployment configuration.
Run preparation validates all role inputs before issuing execution resources.
A native verifier receives its own public inputs and setup authority, independently
of producer witness data. Proof decoding is bounded and consumes each expected
message in order; truncation, trailing bytes and a false acceptance value fail.
Proof files are published atomically. Attempts are explicit producer policies and
retain the generic controller's resource and work accounting.

Only native proof deployment, descriptor, policy and binding version `/4` is
installed, with `zkc.native-origin/2`. Flat, iterated, committed and structured
programs share this model. Deployment admission requires explicit `SetupAuthority`. Quotas are
operational ceilings, separate from the semantic binding root. Capacity and
attempt policy use only `/2` records and `[instructions, iterations]` work pairs. Setup keys retain
authenticated registry authority; this crate does not infer setup authorization
from source text or wire data.

The examples exercise native structured values, nested data, relation composition,
public iteration, authored and external transcripts, independent proof execution,
service custody, retries, domains and setup authority. Tests use the generic
runner and crypto backends; their success is bounded execution evidence.

Build all examples with `cargo build -p zkc-tools --examples --all-features`.
Run Rust tests with `cargo test --workspace --all-features`. Compiler integration
supplies generated native artifacts to the examples. Cryptographic conformance
fixtures are owned by `crates/zkc-test-support/fixtures`.
