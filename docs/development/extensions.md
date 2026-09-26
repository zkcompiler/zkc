# Compiler, runtime and integration maintenance

This guide maps an implementation change to its owners and checks. The
[specification](../spec/README.md) owns meaning; [status](../status.md) owns
support claims. Source-language authoring belongs to the
[language guide](../language/README.md).

## Choose the boundary

| Change | Implementation home | Required connection |
|---|---|---|
| Protocol composed from existing operations | Source definitions and dependencies | Existing admission, projection and execution |
| Mathematical operation or nominal domain | Compiler dialect/contracts, runtime admission, native implementation, Lean interpretation | Independently checked meanings, representations and signatures |
| Alternative implementation of an existing operation | Native bindings, kernels and physical selection | Same operation contract, supported representation and resource behavior |
| IR transformation | Analysis/conversion/transform implementation and pass factory | Input/output stage, retained observations and failure behavior |
| Host application or command | `zkc-tools` application module and thin binary | Explicit inputs, setup authority, checker and execution configuration |
| External formal correspondence | `formal/integrations` package | Exact upstream subject, theorem and hypotheses |

These additions are infrequent. Static registrations, concrete value variants
and explicit dispatch are deliberate. A new abstraction should remove a current
duplication or dependency problem. Use modules before new crates; group code by
its responsibility rather than creating a namespace for every protocol or
upstream library.

## Dialects and operations

[IR.td](../../compiler/include/zkc/Dialect/IR.td) includes the maintained ODS
subjects. Each dialect owns its public `<Name>/IR/<Name>Dialect.h` and its
initialization file under [`lib/Dialect`](../../compiler/lib/Dialect).
[IR.h](../../compiler/include/zkc/Dialect/IR.h) collects shared generated operation
declarations; dialect class declarations live in the per-dialect headers.
Registration and mandatory verification belong to `Zkc::IR`; dialect-local
transformation passes belong to `Zkc::Transforms`; aggregate pass registration
belongs to `Zkc::CompilerCore`. See the [checking boundaries](../compiler/ir-verification.md).
Generated operation declarations stay shared because parent traits cross dialect
boundaries; definitions and registration lists are generated per dialect.
Public dialect queries and verifiers remain extension APIs. Raw construction
helpers under `Dialect/detail/Builders.h` are unsupported same-version details
and do not establish admission. Claim IR structure belongs to IR; the optional
`Zkc::ClaimTranslation` bridge owns source-bound claim import and checking.

For an operation in an existing dialect, edit its ODS definition and verifier.
The generated registration list follows the definition. Bound kernel operations
also declare their logical contract keys on the actual ODS operation record.
`zkc-tblgen` generates the contract-to-operation adapter used by IR; Contracts
remains MLIR-free and independently owns signature and implementation legality.
An explicit family such as `transcript.observe.*` is intersected with installed
contracts. Add independent expected mapping and discriminating behavior checks
when extending it: importer/verifier agreement through the same generated map
cannot detect a shared wrong mapping. No purity or cryptographic law is inferred
from this metadata.

A new built-in dialect
also needs:

1. Its public dialect header and initialization implementation.
2. Entries in `zkc_dialects` and `zkc_dialect_owners` in
   [GenerateIR.cmake](../../compiler/cmake/GenerateIR.cmake), which own generation
   and registration ownership.
3. Membership in the `ProtocolDialects` type list in
   [Registry.cpp](../../compiler/lib/Dialect/Registry.cpp). This list drives both
   `registerDialects` and the loaded-context precondition `hasProtocolDialects`.
4. Its source assigned to `ZkcIR` in
   [Components.cmake](../../compiler/cmake/Components.cmake).

Optional external dialects register in the caller's registry and do not join the
built-in protocol precondition. Keep reusable public headers under `include/zkc`
and implementations under the matching `lib` area.

An operation's mathematical contract, nominal binding and implementation are
separate. Follow [protocol libraries](../compiler/protocol-libraries.md) for the
interactive contract/physical catalogue. The older closed-source
[SourceLibraryInterface](../compiler/libraries.md) is a different carrier; its
independent [service consumer](../../compiler/examples/service/CMakeLists.txt)
demonstrates that specific extension boundary. Neither mechanism loads arbitrary
code named by an input artifact.

## Passes and pipelines

All built-in factories are declared in
[Passes.h](../../compiler/include/zkc/Transforms/Passes.h); tools call
`registerCompilerPasses()` from `Compiler/Passes.h` explicitly. Each implementation owns its name, options,
description, dialect dependencies and statistics. With this small pass set,
ordinary MLIR C++ definitions remain sufficient; there is no second metadata
catalogue or custom registration framework.

[Pipeline builders](../../compiler/include/zkc/Compiler/Pipelines.h) assemble
passes for both `zkc-compile` and `zkc-opt`. The named optimizer pipelines are:

| Pipeline | Input and result | Options |
|---|---|---|
| `zkc-table-pipeline` | Closed-source logical program to direct/physical table plan | `simplify`, `physical=lazy` or `physical=materialized`; absent physical selection keeps logical values |
| `zkc-participant-pipeline` | Common protocol to projected/physical participants | `project-only`, `linear-contractions`, `release-storage` |

Existing individual pass names remain available. Library callers can build a
pipeline without registering global command-line names. Source-bound explicit
implementation selections are validated against the retained common source
before projection; the builder receives the validated choices. The textual
pipeline uses installed defaults, while its C++ builder also accepts those
caller-selected choices.

When adding a pass:

1. Implement the transformation in its owning conversion, analysis or transform
   area and expose a factory in `Passes.h`.
2. Add that factory to [Passes.cpp](../../compiler/lib/Compiler/Passes.cpp) and
   its implementation to the build. Declare any dialects it can create.
3. State the accepted stage, preconditions, observations and failure behavior
   beside the implementation. Preserve or invalidate analyses explicitly if the
   pass uses MLIR's analysis cache.
4. Change [Pipelines.cpp](../../compiler/lib/Compiler/Pipelines.cpp) when the pass
   belongs in a standard route. Keep file I/O and artifact assembly in the host.
5. Test the transformation, an invalid input/precondition, and affected pipeline
   options. [pass_pipelines.py](../../compiler/test/pass_pipelines.py) checks the
   named routes against the driver, including wrong-stage refusal.

Arithmetic equality does not establish preservation of allocation failures,
resource consumption, messages, challenge order or source-bound evidence.
Operation verification and a successful pass run do not prove these laws. Use
the existing [transformation contracts](../compiler/README.md) for such changes.

Compiler tests remain under CTest: small C++ API tests and Python tool checks.
The existing runner already handles IR input, refusal diagnostics and retained
outputs. A separate lit/FileCheck dependency is deferred until a body of static
IR rewrite cases justifies another test surface.

## Runtime and native implementation

The runtime owns admitted control and backend custody. It has no compiler,
cryptographic-library or subprocess dependency. Its two public execution surfaces
remain distinct: finite `Bindings` execution and interactive `Backend` execution.
See the [runtime map](../../crates/zkc-runtime/README.md).

Within [`zkc-backends`](../../crates/zkc-backends/README.md):

| Module | Responsibility |
|---|---|
| `backend/policy.rs` | Explicit host entry and public-input policy |
| `backend/validation.rs` | Shared entry, operand, attribute and output checks |
| `backend/execute.rs` | Explicit dispatch to native implementations |
| `bindings/`, `domains.rs` | Independently advertised signatures and nominal associations |
| `kernels/`, `plonky3/`, `matrix.rs`, `oracle.rs` | Concrete mathematical operations |
| `codec/`, `value.rs` | Canonical wire representation and concrete in-memory values |
| `resource.rs`, `setups.rs`, `transcript.rs` | Authoritative capabilities, setup permission and transcript state |

`NativeBackend::apply` performs common admission, checks public-operand policy,
executes the selected operation, then validates every successful output through
one shared boundary. Kernels still check dependent shapes and preflight expensive
allocations. Failed consumption retains its actual state; frame cleanup runs even
when output validation fails.

An additional implementation may need updates to the explicit dispatch, signature
selection and codecs. A new mathematical domain can also require changes to the
independent compiler/runtime/Lean catalogues. Do not generate all independent
checks from the native implementation. Retain the concrete `Value` enum and opaque
resource handles unless an actual consumer requires a different representation.

### Add an implementation of an existing contract

1. Confirm that the operation's logical signature and nominal associations already
   exist. A new contract is a coordinated compiler/runtime/Lean change, not just
   another dispatch arm.
2. Put the concrete implementation in the existing kernel or provider module.
   Preserve input validation, output preflight and actual resource consumption
   on refusal or exhaustion.
3. Advertise its exact implementation identity and representations in
   `bindings/`; connect it to the explicit dispatch in `backend/execute.rs`.
   `backend/validation.rs` remains the shared entry/result boundary.
4. Update the compiler's physical catalogue/selection and representation
   conversions where needed. Update `codec/` only when the representation needs
   a new wire encoding; an alternative algorithm using the same values does not.
5. Run the affected kernel and backend contract tests, then a source-to-physical
   selection/execution test. Include invalid signatures, representation or
   resource limits relevant to the change. Independent reference comparisons
   remain separate evidence from the native implementation's own checks.

Do not introduce an upstream-specific runtime trait or a new crate solely to
follow this sequence. The current backend trait already isolates execution from
native providers; the concrete modules organize its installed implementation.

## Host tools and external integrations

[`zkc-tools`](../../crates/zkc-tools/README.md) separates application modules from
shared `host` mechanics. `host::io` provides bounded reads; `host::process` owns
one-shot child polling, output bounds and direct-child cleanup. Each checker or
application retains its own command arguments, response decoder, limits and error
codes. Cleanup does not establish descendant isolation or a hard disk quota.

The native workspace's [Cargo.toml](../../Cargo.toml) owns dependency versions;
member manifests select their required features. [Cargo.lock](../../Cargo.lock)
locks resolution. Arkworks helpers, native Plonky3 operations, import adapters and
ArkLib formal correspondence retain separate responsibilities. The
[ArkLib package](../../formal/integrations/arklib/README.md) owns its exact theorem
subjects and premises; it is not a native runtime backend.

[Maintenance](maintenance.md) identifies the owning Lake, Cargo, source and Nix
manifests, including independent benchmark workspaces. Version updates need the
checks for the affected integration; changing a transport hash does not change a
mathematical or cryptographic claim. Runtime settings are explicit host inputs;
[environment configuration](configuration.md) owns development paths and tools.

| Integration | Adapter and pin owner | Relevant validation |
|---|---|---|
| Arkworks | `zkc-arkworks`, native kernels; workspace Cargo manifest/lock | Adapter controls, native backend tests, affected host protocol checks |
| Plonky3 | `zkc-backends/src/plonky3`; workspace Cargo manifest/lock | Numerical/codec controls, nominal bindings and physical selection checks |
| ArkLib / VCVio | `formal/integrations/arklib`; its Lake manifest/lock and matching Nix source pins | Separate integration build and theorem consumers, under their stated premises |

Native changes do not require rebuilding the unchanged optional formal package.
An upstream formal pin or adapter theorem change does require that package's
own checks. Likewise, a native library upgrade needs its affected native and
cross-language controls rather than an unrelated formal rebuild.
