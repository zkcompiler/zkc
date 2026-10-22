# Rust SDK and application Hosts

`zkc` compiles `.zkc` Entry functions into authenticated Host packages. Host
control invokes native protocol/proof deployments and numerical `zkc.program/0`
functions through the generic runtime. The public library separates project compilation, execution owners and shared values:

| Owner | Responsibility |
|---|---|
| `project` | Manifest discovery, source maps, Entry selection, standard paths, template plans and bounded compiler invocation |
| `execution` | Shared `Capacity`, `InputValue`, immutable `PreparedData` and authenticated `ProverMaterial` |
| `entry` | Authenticated packages, named input binding, execution and generated Rust data and callable bindings |
| `run` | Authenticated native run bundles, role preparation, setup authority and application reports |
| `proof` | Independently admitted producer/verifier deployments, public binding, proof execution, attempts and setup authority |

Reusable scheduling, proof execution, bounded framing and driver reports live
in `zkc-runtime::host::{joint,proof,wire}`. Callers import those owners directly;
`NativeBackend` implements their transport contracts in `zkc-native`. This crate
retains independent package/deployment pins, public inputs, setup authorization,
acceptance selection, prepared computation policy, attempts and publication.
Private `host` helpers own byte ingress, native input admission, immutable prover
material, operational capacities, setup validation and bounded compiler-process
execution. No host dispatches on a protocol name.

The separate [`zkc-cli`](../zkc-cli/README.md) package owns command grammar, help and command reports. Project/compiler APIs
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

`Project::settings()` resolves root build/profile/request settings with provenance.
`Compiler::build(CompilationRequest)` returns the package, optional observations,
success diagnostics and local reuse status. `CompilationCache` is an explicit,
quota-bound local store; report requests recompute. These share the CLI's
[tooling contracts](../../docs/compiler/tooling.md). No cached result replaces
Host admission or trusted deployment configuration.

Use `zkc --help` or `zkc COMMAND --help`. The installed commands are:

- `new`, `init`, `prepare`, `check`, `test`, `compile`, `inspect`.
- `run`, `prove`, `verify` (each accepts `--dry-run`), `bindings`.
- `bundle run`, `bundle prove`, `bundle verify`.

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

All proof CLI commands require `--allow-authored` when the selected deployment
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
their success is bounded execution evidence. Build the command-line product with
`cargo build -p zkc-cli --bin zkc`; test providers are disabled by default.
Run Rust tests with `cargo test --workspace --all-features`.

Entry functions use `FunctionInterface`, `FunctionEntry`, `FunctionRequest` and
`FunctionReport`. Their Host control invokes existing numerical, joint and proof
owners; it does not interpret mathematical primitives. Generated `bindings::call`
checks its package pin and returns the typed source result with the complete
native report. The [Python adapter](../../python/README.md) invokes the installed
CLI and uses the same argument/result schema.


Embedding applications depend on `zkc` and use generated `::zkc` bindings or the
typed Entry APIs. Precompiled package execution requires neither a compiler nor
the CLI. `project::Compiler` is an explicit bounded subprocess service for source
compilation; it is selected separately from execution.

`files::read_regular` distinguishes I/O refusal from byte-limit refusal.
`entry::files::Documents` retains directory-confined input descriptors and shares
aggregate decoding limits across argument and invocation inputs.
`entry::files::Invocations` loads child policy and setup material under each
child's independent authority, then encodes results using the checked material.
`ProofEntry::prepare_file_call` retains the selected proof operation and checks
requested result codecs and setup material before candidate proof bytes are read.
It retains invocation imports through execution and result encoding. Preparation
and execution preserve typed Entry errors; reports survive later encoding failures.

`files::Outputs` protects selected paths and opened input identities. Its separate
`publish` and `create` operations stage all buffers, then replace or create each
file atomically. Typed `Publication` receipts and `PublicationError` retain the
ordered successful prefix, failure stage and failed item; callers must preserve
those receipts when publishing several batches. Creation never clobbers an
existing file. The CLI alone renders receipts as command JSON.

The [installed Rust consumer check](../../common/tests/check_rust_sdk.py) stages
SDK sources and Unicode data, builds an independent normal-feature application,
and executes prepared numerical, joint and proof packages outside the checkout
with no compiler or CLI on `PATH`.
