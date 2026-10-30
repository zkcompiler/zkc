# Virtual machine

`vm::Program::decode(bytes, &contracts)` admits `zkc.program/0` into immutable typed VM code. It
checks all retained definitions and prepares local positional operands, region
layouts and operation bindings without consulting a backend. Participant code
uses named SSA registers and loop-input layouts retained by the same admission
walk. Both forms retain the admitted structured control;
there is no second serialized format.

The Program retains its trusted immutable `Contracts`, including execution policy.
`ContractsBuilder` extends the existing operation inventory with exact trusted
physical realizations, mathematical layouts and bounded aggregate families. Logical erasure and
attributes are checked by the runtime against the shared typed declaration catalog.
The catalog supplies scoped signatures, requirements, parameter schemas, history
facets and type permissions. Runtime domain facts and its closed interpretation
profile remain explicit; declaration membership never installs an implementation.
Physical adapters have separate erasures and cannot enter as logical operations.
Catalog-scoped
extension IDs cannot be substituted across independently built contexts.
`Contracts::standard(policy)` explicitly supplies the fixed Native inventory;
`Contracts::with_policy` preserves identity without altering admitted programs.
Names and declared signatures in artifact bytes confer no installation authority.
The fixed Boolean/index constructors and existing affine and capacity rules remain
VM contracts. Complete aggregate types retain all selected child layouts,
including inactive variant alternatives, separately from their logical schema.
Generic sequence and dense operations specialize these types through checked
physical arguments. Unknown storage, mismatched children and aggregate conversions
without an installed law refuse admission.

Wire permission is a separate positive contract. The standard context owns
sequence and variant frames; every selected child still needs codec permission.
An empty context needs an exact container grant or a contributed frame family,
as well as every child grant. Fixed vectors remain local-only. Preparation
eligibility is independent of wire permission and excludes live resources.

`Program::check_installation` optionally checks backend availability before a
Host admits a deployment. Every execution independently links its owned backend.
The internal `Instance` owns complete invocation loading, installed handles,
reached-call preparation, frame identity and nesting, retained storage, budgets
and work accounting. Code can be shared;
mutable execution state and resource authority cannot.

The [interpreter](../interpreter/) owns instruction walking, value environments,
continuations and pending actions. It invokes the instance for operations,
services, frame transitions and accounting. The instance never reads interpreter
environments. An installed operation receives only its admitted binding,
explicit operands and current call context. Installed operations include effects;
installation alone does not establish numerical purity.

`NativeProofEntry::new` admits a combined producer/validator deployment.
`new_for_operation` admits exactly one endpoint selected by
`NativeProofOperation::{Prove, Verify}` using the same transcript, construction,
dependency and wire rules. Its public source-input indices come from the
authenticated descriptor; an absent endpoint needs no source map or executable
substitute. `producer()` and `validator()` return optional admitted endpoints;
`producer_role()` and `validator_role()` retain descriptor identities for context
binding. Those identities do not authorize execution. The caller authenticates
the descriptor and its correspondence to each present role's wire layout.

Operation-specific codec admission requires only the selected direction's
helpers and validates every retained codec declaration. Proof execution uses
`Program::check_role_installation` and `Runner::new_for_role_with_ledger` to link
all potential calls and regions of the selected endpoint. The combined
constructor and full-program installation remain available for low-level callers.

`Backend::Operation: InstalledOperation` names the installed handle contract.
`prepare_binding` resolves one exact `OperationBinding`; `OperationSignature`
describes ports and attributes, with `BoundSignature` using physical port types.
Extension handles report their independently installed `ImplementationId` and
`ImplementationRequirements`. Before frames, linking checks actual ports,
identity and timing premises against expected contracts and explicit policy.
Timing authorization never follows from role, determinism or provider name.
Dynamic checks and resource transitions remain in backend execution hooks.

Inside `instance`, `loading` admits the initial invocation and participant
arguments; `frames` owns typed loop-frame construction, entry and terminal
cleanup; `values` owns validation, scopes and
owned return handoffs; `preparation` owns deterministic classification, recording
snapshots and replay. Handoffs must be consumed through their originating VM.
The interpreter supplies public control provenance and never constructs a work
snapshot or adjusts a backing reference count.

## Owners

| Module | Responsibility |
|---|---|
| `decode`, `model`, `admit` | Exact artifact decoding and structural admission |
| `code` | Typed VM instructions and shared local execution layouts |
| `link` | Independent installation checks for exact bindings and services |
| `instance` | Per-execution backend, frame and capacity ownership |
| `backend`, `bindings`, `contracts`, `operations` | Value, frame and trusted admission/installation contracts |
| `retention` | Shared immutable backing and validation evidence |
| `preparation` | Bounded storage for certified public computations |
| `program`, `observe`, `native_proof` | Static layout, runtime observations and proof-policy inspection |

The [VM contract](../../../../docs/spec/runtime/vm.md) defines execution and
failure obligations. [Capacity](../../../../docs/spec/runtime/capacity.md) owns
metering and retained storage. The [backend guide](../../../zkc-cpu/README.md)
owns native providers and their trust boundary.
