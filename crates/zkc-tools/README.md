# Entry and native execution hosts

`zkc` compiles `.zkc` Entry packages through the mathematical compiler and executes
the resulting `zkc.program` with the generic runtime. The public library has
three owners:

| Owner | Responsibility |
|---|---|
| `entry` | Authenticated packages, named input binding, execution and generated Rust data bindings |
| `run` | Authenticated run bundles, role preparation, scheduling, transport and bounded reports |
| `proof` | Independently admitted producer/verifier deployments, public binding, proof execution, attempts and setup authority |

`proof` also exports bounded proof readers/writers and execution reports.
Private `host` helpers own byte ingress, native input admission, immutable prover
material, operational capacities, setup validation and bounded compiler-process
execution. No host dispatches on a protocol name.

The `cli` module owns discovery, compilation subprocesses, file transport and
command reports. Reusable execution APIs remain in the three owners above.

Use `zkc --help` or `zkc COMMAND --help`. The installed commands are:

- `compile`, `run`, `prove`, `verify`, `bindings`.
- `run-bundle`, `prove-bundle`, `verify-bundle`.

An expected SHA-256 comes from trusted compilation or deployment configuration.
Run preparation validates all role inputs before issuing execution resources.
A native verifier receives its own public inputs and setup authority, independently
of producer witness data. Proof decoding is bounded and consumes each expected
message in order; truncation, trailing bytes and a false acceptance value fail.
Configured input files must be bounded regular files. Output symlinks and aliases
of inputs or other outputs (including hardlinks) refuse. All requested outputs
are encoded and staged before per-file atomic replacement; a later rename failure
reports exactly which earlier files were published. No multi-file transaction is
claimed. On Unix, published files retain the staging tempfile's `0600` permissions,
including when replacing an existing destination; previous destination permissions
are not preserved. Attempts are explicit producer policies and
retain the generic controller's resource and work accounting.

All proof CLI commands require `--allow-header-only` when the selected deployment
has no compiler-derived transcript. Bundle refusal reports `binding_scope: header`.
This opt-in does not replace an independently trusted deployment pin or establish
cryptographic transcript binding. Low-level native proof execution APIs leave that
policy to their caller.

Native proof deployment, descriptor, policy and binding each have one current
schema, with `zkc.native-origin` occurrences. Flat, iterated, committed and structured
programs share this model. Deployment admission requires explicit `SetupAuthority`. Quotas are
operational ceilings, separate from the semantic binding root. Oversized limit
requests refuse instead of being silently clamped; public limit types expose
installed hard maxima and document their independent units. Capacity and
attempt policy use `[instructions, iterations]` work pairs. Setup keys retain
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
