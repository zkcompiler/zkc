# Virtual machine

`vm::Program::decode` admits `zkc.program/0` into immutable typed VM code. It
checks all retained definitions and prepares local positional operands, region
layouts and operation bindings without consulting a backend. Participant code
uses named SSA registers. Both forms retain the admitted structured control;
there is no second serialized format.

`Program::check_installation` optionally checks backend availability before a
Host admits a deployment. Every execution independently links its owned backend.
The internal `Instance` owns installed handles, reached-call preparation, frame
nesting, retained storage, budgets and work accounting. Code can be shared;
mutable execution state and resource authority cannot.

The [interpreter](../interpreter/) owns instruction walking, value environments,
continuations and pending actions. It invokes the instance for operations,
services, frame transitions and accounting. The instance never reads interpreter
environments. An installed operation receives only its admitted binding,
explicit operands and current call context. Installed operations include effects;
installation alone does not establish numerical purity.

## Owners

| Module | Responsibility |
|---|---|
| `decode`, `model`, `admit` | Exact artifact decoding and structural admission |
| `code` | Typed VM instructions and shared local execution layouts |
| `link` | Independent installation checks for exact bindings and services |
| `instance` | Per-execution backend, frame and capacity ownership |
| `backend`, `bindings`, `operations` | Value, frame and installed-operation contracts |
| `retention` | Shared immutable backing and validation evidence |
| `preparation` | Bounded storage for certified public computations |
| `program`, `observe`, `native_proof` | Static layout, runtime observations and proof-policy inspection |

The [VM contract](../../../../docs/spec/runtime/vm.md) defines execution and
failure obligations. [Capacity](../../../../docs/spec/runtime/capacity.md) owns
metering and retained storage. The [backend guide](../../../zkc-backends/README.md)
owns native providers and their trust boundary.
