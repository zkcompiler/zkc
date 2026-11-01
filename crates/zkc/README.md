# Rust SDK and application Hosts

Applications depend on `zkc` and execute authenticated packages through reusable
Hosts. Generated Rust bindings call the SDK directly. Already compiled packages
need neither the compiler nor the `zkc` executable at execution time.

Native proof admission consumes one current version-zero schema: a twelve-field
policy with explicit per-occurrence gates and an eight-field descriptor with
construction-owned witness records. Gates bind the selected source query,
bound, count and difficulty; witness records bind the executable index slot and
codec. The complete descriptor, public statement and caller context enter the
existing invocation binding. Regenerate affected packages when this schema changes.
Explicit gate selection uses the pinned `NativeDeployment` API. Source-bound
`ProofEntry` admission requires empty gates until its source interface represents
that selection.

## Compile and generate bindings

Source compilation requires an installed `zkc-compile`; command-line preparation
also requires `zkc` from [`zkc-cli`](../zkc-cli/README.md). The development checkout
can build these with `just build`, or package them with
`nix build .#compiler .#tools`. See [installation](../../docs/development/README.md)
for toolchains and installed consumers. The SDK dependency is separate:

```toml
[dependencies]
zkc = { path = "/path/to/zkc/crates/zkc" }
```

For example, save this as `main.zkc`:

```zkc
module application;
entry fn Twice(value:index) { return value + 2; }
protocol Equality roles(P,V)(expected:bool@(P,V),candidate:bool@P)->(accepted:bool@V){
  let received=send P->V(candidate);
  let accepted@V=received==expected;
  return accepted;
}
proof Core=Equality{
  prover P;verifier V;public{expected};accept accepted;construction authored;
}
```

Compile and generate the two bindings beside your application's Rust source:

```sh
zkc compile application::Twice --module=application=main.zkc --output=numerical.zkpkg
zkc compile application::Core --module=application=main.zkc --output=proof.zkpkg
# Use each package_sha256 from the trusted compilation report below.
zkc bindings --package=numerical.zkpkg --sha256=NUMERICAL_SHA256 --output=numerical.rs
zkc bindings --package=proof.zkpkg --sha256=PROOF_SHA256 --output=proof.rs
```

Bindings contain a package pin, source-shaped argument/result types, and an
`admit` function. Function bindings also supply `call`. Regenerate them when the
authorized package changes. The expected pin comes from trusted compilation or
deployment configuration; hashing an untrusted candidate does not authorize it.

## Admit, prepare and execute

With those generated files and packages beside `main.rs`, this application
prepares a numerical call, reuses its admitted Host, and verifies a proof against
an independently supplied, nonempty statement:

```rust
#[allow(dead_code)]
mod numerical { include!("numerical.rs"); }
#[allow(dead_code)]
mod proof { include!("proof.rs"); }
use zkc::entry::{
    BindingPolicy, FunctionRequest, ProofOperation, ProofOptions, ProofRequest, RoleInputs,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let host = numerical::admit(
        include_bytes!("numerical.zkpkg"), Default::default(), Default::default(),
    )?;
    let prepared = host.prepare(FunctionRequest {
        arguments: numerical::Arguments { value: 7 }.into(),
        context: Default::default(),
    })?;
    let report = prepared.execute();
    assert!(report.is_success(), "{}", report.diagnostics());
    for value in [7, 11] {
        let result = numerical::call(
            &host, numerical::Arguments { value }, Default::default(),
        )?;
        assert!(result.report.is_success());
        assert!(result.conversion_error.is_none());
        assert_eq!(result.value, Some(value + 2));
    }

    // This example explicitly authorizes an authored proof binding policy.
    let options = ProofOptions {
        binding: BindingPolicy::AllowAuthored, ..Default::default()
    };
    let bytes = include_bytes!("proof.zkpkg");
    let prover = proof::admit(bytes, options.clone(), Default::default())?;
    let verifier = proof::admit(bytes, options, Default::default())?;
    let proving = || ProofRequest {
        public: proof::PublicInputs { expected: true }.into(),
        private: RoleInputs {
            inputs: proof::PInputs { candidate: true }.into(), ..Default::default()
        },
        ..Default::default()
    };
    prover.check_inputs(proving(), ProofOperation::Prove, None)?;
    let produced = prover.prove(proving())?;
    assert!(produced.is_success());
    let candidate = produced.native.outcome?;
    let checked = verifier.verify(ProofRequest {
        public: proof::PublicInputs { expected: true }.into(),
        ..Default::default()
    }, &candidate)?;
    assert_eq!(checked.verification_result(), Some(true));
    assert!(checked.is_success());
    Ok(())
}
```

Admission retains immutable package identity and checks the executable, interface
and limits. Preparation checks arguments and invocation policies before execution
resources are issued. `check_inputs` performs preparation and discards the plan;
it does not execute or publish results. Prepared calls borrow their Host. Create
a fresh request for each call; there is no implicit retry. Reusable immutable
material does not retain invocation authority or reservations.

An automatic protocol Entry or a closed generic selector such as `Echo<index>`
also generates function bindings. For functions with child deployments, inspect
`FunctionInterface::deployment_interfaces(&package)`, supply a `SetupAuthority`
for each exact child ID at admission, and supply matching `InvocationBinding`
values in `InvocationContext` when preparing. Ordinary source arguments cannot
replace setup authority or child policies. `RunContext` defaults to a fresh
OS-random session per reached call; explicit session freshness belongs to the
application.

## Memory and optional adapters

Default features are `cpu`, `project` and `parallel`. With
`default-features = false`, the SDK retains package capture, source-interface
inspection and input schemas without linking the VM, CPU backend or numerical
kernels. Capture and metadata checks do not admit a program for execution.

| Feature | Adds |
|---|---|
| `files` | Bounded file I/O and atomic artifact publication |
| `project` | Manifests, source capture and the compiler subprocess service; implies `files` |
| `cpu` | Native admission, typed execution, proof and joint Hosts, memory input decoding and result encoding |
| `parallel` | Bounded CPU workers; implies `cpu` |

Use `features = ["cpu"]` with defaults disabled for in-memory inline execution.
Add `files` for confined file references; project compilation is optional when
an authenticated package is already available.

`entry::memory::ProofCallOptions` and `ProofEntry::preflight_memory_call` use the
same schema decoder, setup authority and proof Host as file calls. An explicit
map of immutable `Arc<Vec<u8>>` bindings resolves document references; names
confer no filesystem access or setup authority. `SetupAuthority::from_bytes`
parses independently authorized setup pins. CPU material imports are reusable
only for identical material, pin, bounds and installation; invocation authority
and resource reservations are checked anew. Result encoding returns a guarded
envelope; retain it through the transport copy or publication.

`execution::CpuInstallation` composes the known providers before admission.
`ProofOptions::with_installation` and the corresponding function/Host options
retain that view through nested calls, services, input decoding and result
encoding. The [CPU backend](../zkc-cpu/README.md#provider-composition) documents
selection and the matching compiler target descriptor. This support policy is
separate from numerical worker ownership.

## CPU execution

With `parallel`, create `zkc::execution::CpuExecution::new(workers)?` with `1..=256` workers and
pass it as the last argument to `admit_with_cpu` on `RunHost`,
`NativeDeployment`, `RunEntry`, `ProofEntry` or `FunctionEntry`. For example:

```rust,ignore
let cpu = zkc::execution::CpuExecution::new(4)?;
let host = zkc::entry::RunEntry::admit_with_cpu(package, limits, setups, cpu.clone())?;
```

Admission backends, input imports, numerical calculations, child deployments,
participants, proof roles and retries share clones of that owner from
construction onward. `ProofEntry::admit_operation_with_cpu` admits a selected
proof operation. All five Hosts expose `cpu()` and `with_cpu` for rebinding an
idle admitted Host; use `admit_with_cpu` when the context is known at construction
to avoid creating an unused default pool. CPU ownership stays outside the
limit and option structs.

With `parallel`, each default `admit` creates one fresh, explicitly owned one-worker pool before
admission. Each independent `CpuExecution::serial()?` also creates a fresh pool;
there is no process-global singleton. Clone a context to share one worker
ceiling between independently admitted Hosts. `PreparedData` constructors and
Entry result encoders also offer variants ending in `_with_cpu`;
`FunctionResultEncoder::encode_with_cpu` and proof results preserve sharing
through serialization.

`cpu.enter` supplies the context lexically while validation, imports, partial
effects and VM control remain ordered on the calling thread. Kernel numerical
phases select work for its pool. The worker count bounds only that context's
numerical workers; caller threads, other contexts and foreign threads are
outside the ceiling. Dropping the last clone requests Rayon worker shutdown;
drop does not guarantee that worker threads have joined. CPU policy is separate
from capacity, authority, invocation data and artifact identity. The SDK does
not read Rayon environment variables to select its worker count.

Without `parallel`, only a worker count of one is accepted. Numerical work runs
inline on the caller, including `serial()` and default admission; no pool is
created. This is the browser build's execution policy.

## Proof authority and outcomes

The verifier selects its trusted package, acceptance port, public inputs, context
and setup authority independently of candidate proof bytes and producer witness.
`SetupAuthority::default()` authorizes no setup slots; setup-bearing deployments
require independently pinned registry/key material. Generated types describe
data shape and do not grant authority.

Public data uses the complete physical types selected by the admitted Program,
including inactive variant children. Producer and validator occurrences of a
shared public source port must select the same physical type. Named and
positional calls decode wire data into that selection and require Native and
Prepared values to match it exactly; source constructor and custody checks still
apply. Public binding uses the canonical native bytes for the logical value.
This admission requires an installed native wire codec for the complete type.

The default `BindingPolicy::TranscriptRequired` requires compiler-derived
transcript binding. The example's `AllowAuthored` opts into the protocol author's
binding policy and Host header checks. It does not establish cryptographic
transcript binding or security. CLI proof calls require the corresponding
`--allow-authored` opt-in. See [proof jobs](../../docs/runtime/proofs.md).

`EntryError` retains a stable `code()` and `EntryPhase` for admission and
preparation failures. Execution failures retain usage, reached calls and native
diagnostics in `FunctionReport` or `ProofReport`. Inspect `is_success()` before
using an output. Generated `CallResult` keeps the full report and a separate
`conversion_error`; its `value` is absent on failed execution or conversion.
A completed child proof followed by a stopped outer Entry remains in the report,
but the outer source result is withheld.

For direct proof verification, `verification_result()` distinguishes accepted
(`Some(true)`), a completed negative verifier result (`Some(false)`), and failure
to reach that result (`None`). A negative result has `is_success() == false`.
Changing the independent statement refuses with `proof-header`; it cannot be
used to reinterpret a candidate. A source `Core::verify` call instead returns its
source `Accepted` or `Rejected` variant when verification completes, so a
`Rejected` value can be the successful result of the outer function.

## Independently installed backends

`entry::BackendRun` binds an authenticated run package to an explicit immutable
`zkc_runtime::vm::Contracts` context and an independently installed
`WireBackend`. It checks the source interface and logical participant ABI, then
reuses the Runtime joint Host. Calls supply typed backend values in that ABI's
order. Each executing backend is linked independently before frame entry.

This small adapter supports data-only run packages. Setup assets, services and
proof packages require their owning adapters and refuse here. Typed values do
not bypass source constructor or custody restrictions. Native applications keep
the named, schema-driven `RunEntry` and `FunctionEntry` APIs described above.

## Files and optional compiler service

The SDK does not resolve data paths implicitly. `entry::files::Documents` opts
into bounded regular JSON documents and directory-confined value references,
sharing aggregate decode limits. `entry::files::Invocations` imports child
policies and setup material under their independent authorities.
Its `into_parts` transfers admission pins, decoded invocation context and a result
encoder that retains the original capacity and authenticated setup material.
`ProofEntry::preflight_call` retains the selected operation, input imports and
result codecs through execution and encoding. It checks requested codecs and setup
imports before reading candidate proof bytes; request validation and execution
preparation occur during `execute`. Errors retain their phase and code.

`files::Outputs` protects input identities and selected paths. `create` never
clobbers; `publish` stages all buffers before per-file atomic replacement. Keep
`Publication` and `PublicationError` receipts: a later failure can leave an
already published prefix. This is not a multi-file transaction. On Unix,
published files use the staging file's `0600` permissions. Dry-run CLI operations
check inputs without publishing proof or result files.

Applications that compile source can opt into the bounded compiler subprocess
service explicitly:

```rust
fn compile(project_path: &std::path::Path, executable: &str)
    -> Result<zkc::entry::Package, Box<dyn std::error::Error>>
{
    use zkc::project::{Compiler, Project, Selection};
    let project = Project::load(project_path)?;
    let compiler = Compiler::new(executable)?;
    let options = project.settings(None, &Default::default())?.options();
    let package = compiler.compile(
        &project, Selection { name: Some("Twice"), kind: None }, options,
    )?;
    Ok(package)
}
```

`Compiler::prepare` returns checked interfaces and template plans without writing
files. `Compiler::build` adds optional observations, diagnostics and explicit
bounded compilation caching. These operations require the compiler; execution
of their returned package uses the same admission APIs as precompiled inputs.

| Module | Owner |
|---|---|
| `project` | Source maps, manifests, compiler service and preparation plans |
| `entry` | Package pins, named values, bindings and function/proof Hosts |
| `execution` | CPU contexts, capacity, immutable prepared data and authenticated prover material |
| `run`, `proof` | Native deployments, setup/public authority and typed execution reports |

The CLI owns argument grammar and command reports. Canonical trees, proof framing
and immutable binding serialization live in `zkc-format`. Scheduling, live
reservations and metered transport live in `zkc-runtime::host`; native adaptation
lives in `zkc-cpu`.
The [generated consumer](../../common/tests/protocol/test_rust_sdk.py) and
[staged SDK consumer](../../common/tests/check_rust_sdk.py) build independent
normal-feature applications and execute outside the checkout without compiler
or CLI on `PATH`. See [test selection](../../common/tests/README.md#selecting-checks).

## Portable execution

The SDK's default `parallel` feature forwards bounded CPU execution to the
native backend and kernels. A dependency with `default-features = false,
features = ["cpu"]` executes numerical phases inline and accepts only
`CpuExecution::new(1)`.
Cargo features are additive; all consumers in that build must preserve the
nonparallel selection. The [browser adapter](../zkc-web/README.md) supplies a
small in-memory proof API and browser entropy without changing package bytes
or importing filesystem capabilities.

## EVM verifier compilation

The optional `evm` feature enables compiler-backed EVM artifacts without a CPU
runtime or EVM engine dependency. Applications executing those bytes choose their
own chain client or engine. Compile from the same checked proof Entry:

```rust,ignore
use zkc::{evm::{Invocation, Options, Solc}, project::{Compiler, Project, Selection}};
fn compile_verifier(
    trusted_solc_sha256: &str, public_wires: &[&[u8]], proof: &[u8],
) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let project = Project::load("examples/projects/sumcheck-keccak/zkc.toml")?;
    let compiler = Compiler::new("/absolute/path/to/zkc-compile")?;
    let solc = Solc::new("/absolute/path/to/solc", trusted_solc_sha256)?;
    let artifact = compiler.build_evm(
        &project, Selection { name: Some("example::Proof"), kind: None },
        &Options::default(), &solc, None,
    )?;
    let manifest_sha256 = artifact.identity(); // Retain independently.
    artifact.publish("build/verifier.evm")?;
    Ok(artifact.calldata(Invocation {
        public_inputs: public_wires, context: b"application", proof,
    })?)
}
```

`Options::default()` selects Cancun and the common compiler defaults. Set
`fork: evm::EvmFork::Prague` explicitly for Prague; `compile` carries shared
mathematical/oracle settings. The source response, solc request and authenticated
artifact retain those effective selections.

On Linux, EVM compilation executes sealed snapshots of the compiler and solc;
the executable hash describes those exact bytes. Script interpreters and dynamic
libraries remain trusted, mutable host toolchain inputs. For a compiler resolved
under `<prefix>/bin`, sealed execution prepends `<prefix>/lib` to the child's
`LD_LIBRARY_PATH`, followed by any nonempty ambient value. This restores the
compiler installer's `$ORIGIN/../lib` lookup with installation libraries taking
priority over ambient libraries. Other loader rules still apply, including
legacy `DT_RPATH` precedence and expansion of tokens in the ambient value.
Compiler descendants inherit this search path. An unset or empty ambient value
adds no current directory search. Installation prefixes containing `:`, `;` or
`$` refuse with `source-compiler-io` because the loader cannot encode them
literally here. This compiler layout policy does not apply to solc or other
executable snapshots.

Retain `manifest_sha256` independently. A later
`evm::Artifact::capture(directory, expected_manifest)` authenticates the exact
manifest and validates its file inventory, hashes, source, settings and code-size
limits. `creation_bytecode()` and `runtime_bytecode()` expose immutable binary
bytes. `calldata()` encodes `verify(publicInputs, context, proof)` from the existing
canonical wire values and native framed proof; it does not reinterpret them.
The [target contract](../../docs/spec/targets/evm.md) defines supported operations,
outcomes, ceilings, tool pins, authenticated reuse and atomic publication.
