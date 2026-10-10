# Entry and native execution hosts

`zkc` compiles `.zkc` Entry packages through the mathematical compiler and executes
the resulting `zkc.program/0` with the generic runtime. The public library separates project compilation, execution owners and shared values:

| Owner | Responsibility |
|---|---|
| `project` | Manifest discovery, source maps, Entry selection, standard paths, template plans and bounded compiler invocation |
| `execution` | Shared `Capacity`, `InputValue` and immutable `ProverMaterial` |
| `entry` | Authenticated packages, named input binding, execution and generated Rust data bindings |
| `run` | Authenticated run bundles, role preparation, scheduling, transport and bounded reports |
| `proof` | Independently admitted producer/verifier deployments, public binding, proof execution, attempts and setup authority |

`proof` also exports bounded proof readers/writers and execution reports.
Private `host` helpers own byte ingress, native input admission, immutable prover
material, operational capacities, setup validation and bounded compiler-process
execution. No host dispatches on a protocol name.

The `cli` module owns command grammar, help and reports. Project/compiler APIs
return typed results; CLI adapters coordinate them with Entry preparation and
publication. `entry::Interface` is a checked logical view; `BoundInterface` binds
that view to a package. `entry::inputs` derives readable input groups and schemas
from the same view, with explicit opt-in file resolution. Native value import
and resource accounting remain in the common Host.

`Project::layout()` resolves standard project paths. `Compiler::prepare()` returns
checked interfaces and `Template` files without publishing them; the CLI creates
missing templates through the Host's no-clobber publication API. Execution first
resolves explicit options and defaults, then uses the same input decoder and
admission path. Human output and `--json` render the same command report.
`Compiler::check()` accepts `CheckOptions` for declaration and notation inventories;
`NotationOptions` selects private and installation records. These are diagnostic
views and do not change execution semantics.

Use `zkc --help` or `zkc COMMAND --help`. The installed commands are:

- `new`, `init`, `prepare`, `check`, `compile`, `inspect`, `inputs init`, `inputs check`.
- `run`, `prove`, `verify`, `bindings`.
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
schema, with `zkc.native-origin/0` occurrences. Flat, iterated, committed and structured
programs share this model. Deployment admission requires explicit `SetupAuthority`. Quotas are
operational ceilings, separate from the semantic binding root. Oversized limit
requests refuse instead of being silently clamped; public limit types expose
installed hard maxima and document their independent units. Capacity and
attempt policy use `[instructions, iterations, logical_bytes]` work triples. Setup keys retain
authenticated registry authority; this crate does not infer setup authorization
from source text or wire data.

The [integration drivers](../zkc-test-drivers/README.md) exercise this SDK against
compiler-generated programs. They use the generic Runner and installed backends;
their success is bounded execution evidence. Build the product with
`cargo build -p zkc-tools --bin zkc`; test providers are disabled by default.
Run Rust tests with `cargo test --workspace --all-features`.
