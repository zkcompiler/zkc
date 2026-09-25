# Closed source libraries and dependent replies

The direct compiler selects a consumer-installed
source library from the entry's exact ordered dependencies. Rust checks each
operation result before the source continuation runs. The independent adapter
also checks provider replies before using them inside a composite operation. The independent `vector-service/1` consumer exercises these
interfaces alongside `table-protocol/1`.

This supplies the finite library/reply boundary in [integrated admission](calls.md#6-integrated-admission-responsibilities).
Open-template binding and general endpoint admission remain separate work.
Physical table selection and stateful admission have their own bounded consumers.

## Compiler installation and resolution

[`SourceLibraryInterface`](../../compiler/include/zkc/Interfaces/SourceLibrary.h) supplies
the dependency set, type codecs, condition sort and operation resolution. A
resolved operation records its concrete MLIR name, input/result types, attributes
and ordering requirement. One model may describe several dialects: the table
model covers algebra, polynomial and protocol operations.

The implementation uses an MLIR
[dialect interface](https://mlir.llvm.org/docs/Interfaces/#dialect-interfaces),
while each actual operation exports its descriptor through `SourceOpInterface`.
The generic importer, verifier, structured control conversion and exporter use
these interfaces. An added library does not need another copy of those passes.

The consumer must load all selected library models and their dependent dialects
before parsing or running passes. `runCompiler` loads the supplied registry;
resolution examines the loaded models and borrows their context-owned interfaces.
`registerDialects` registers carriers only; the default tools explicitly install
`registerTableLibrary`. A consumer may instead install just its own library.
Registration must remain fixed during compilation. Descriptors cannot request
plugin loading, checker executables or runtime provider replacement.

Resolution requires exactly one matching model. Unknown revisions, incomplete
dependency sets and duplicate identities refuse; two matching loaded models are
ambiguous. Export verifies that the selected descriptor resolves to the **actual
operation name, attributes and signature**. A same-spelled descriptor from another
operation does not establish identity. The enclosing program's region verifier
resolves the context once and validates every nested operation, including dormant
branches. Individual operation verifiers check ODS structure and enclosure; they
do not establish closed-library membership in isolation. Export reuses the same
resolved identity/signature check without reparsing the context per operation. The negative-control service operation
has the correct descriptor and signature but a different MLIR name, and is refused.

This is a closed-model installation mechanism. It does not yet compose arbitrary
open slot environments or select multiple revisions on the same dialect interface.
Those belong to [component binding](components.md). Their resolved result can
feed this boundary, but the boundary is not their implementation.

## Runtime validation

There are two distinct checks:

1. [`Bindings::validate_result`](../../crates/zkc-runtime/src/execution.rs) checks
   the **final source-operation result** against the actual operation arguments,
   after static sort validation and before binding that result in the source.
2. The adapter checks **each provider-interface reply** before consuming it.
   The generic operation dispatcher cannot inspect intermediate replies hidden
   inside `invoke`. The service's private `call` method enforces this boundary.

```text
invoke source operation(arguments)
  provider call(request₁) → validate reply₁ → internal continuation
  provider call(request₂) → validate reply₂ → internal continuation
  returned(value)         → validate sort and operation result
                          → source continuation
```

An operation may use zero, one or several calls. `request_and_send(n)` requests a
vector, sums its entries and sends the sum, returning only the final Boolean.
The first vector must have length `n` and entries below seven **before the sum or
send executes**. This exemplifies Lean's request-indexed `Reply` inside the
operation's `Proc`; a final predicate check cannot establish that vector property.
For a send, the reply must equal whether its actual count is zero. A valid `false`
is a returned value; the caller decides whether to stop.

A malformed provider reply interrupts host execution. `Completed` retains the
actual bindings, state updates and events from the call; the suffix does not run.
A logical stop likewise retains its actual reason and effects. These rules apply
to intermediate calls and inside binding and repeat regions. The example CLI
reports `admission-failed`, `binding-failed`, `start-failed` and `interrupted`
separately; the first three preserve the state before protocol execution.

Both checks enforce declared value constraints, not the full transition law.
They do not prove arithmetic correctness, freshness, framing, distribution or
provider state correspondence. An altered but well-shaped vector passes legality
and disagrees with the selected Lean provider; differential testing detects it.
Composite adapters remain trusted to route every reply through the appropriate
check. No one-call restriction was added to the source semantics or runtime API.

The service's request counts are owned immutable values. For a future mutable
storage adapter, the request data needed by validation must be pinned or retained
before the call changes storage. Cloning an opaque handle alone is not a logical
snapshot. That representation obligation belongs to the adapter and its complete
operation contract, not to the generic dispatcher.

## Independent consumer

The [Lean example](../../formal/Examples/VectorService/README.md) uses a static
source vector sort but a genuinely dependent interpreted reply:

```text
request(n) : { xs : List (Fin 7) // xs.length = n }
send(n)    : { b : Bool // b = decide (n = 0) }
```

This is an instance of the existing typed source/interpretation semantics. Lean's
reply type carries the dependency. Native execution validates the corresponding
owned vector before making it available to the continuation. A later request
uses the sum of an earlier vector, so its length cannot be fixed in the source
type. The MLIR condition type is `!service.predicate`, not a hardcoded `i1`.

The [C++ consumer](../../compiler/examples/service/CMakeLists.txt) can build
against the installed `Zkc::Compiler` package. The
[Rust consumer](../../crates/zkc-tools/examples/vector-service/main.rs) installs
its own library and the existing Lean checker adapter. Neither adds service
operations to the production table vocabulary.

The example is a deterministic service, not a new cryptographic protocol. It
refuses vector requests above 1024 entries before calling the provider. Each
actual external call updates a counter and records an event, including a call
that exhausts the supplied tape. This makes stopped state observable in tests.

The native example additionally limits vectors passed to `sum` to 1024 entries
during capacity estimation, including a dormant branch. Its abstract vector
`top` is relative to the admitted byte budget, not this request/operation limit. Lean can execute larger
input vectors. That difference is an explicit host admission limit; it is not
silently added to the protocol's mathematical meaning. The suite records both
the native refusal and the corresponding Lean execution.

## Remaining work

Differential execution over adaptive shapes, custom conditions, closed-family
identity, structured control and malformed replies after writes establishes
bounded native correspondence, not a proof of the compiler or a security theorem.

The [stateful table consumer](phase-admission.md#stateful-table-admission) binds
an actual role and recorded entry phase. Reply legality and phase conformance
remain separate checks; that fixed-prover application is not general endpoint
admission or a provider-invariant proof. Physical storage/kernel selection must
preserve the checked shapes under its own representation contract.
