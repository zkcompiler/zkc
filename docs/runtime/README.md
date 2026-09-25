# Execution and backend integration

Rust consumes admitted participant or plan artifacts and executes their selected
operations through backend adapters. The C++/MLIR compiler owns transformation
and implementation selection. Lean supplies independent checking and reference
execution at the scopes in [status](../status.md).

| Task or boundary | Reference |
|---|---|
| Run a compiled protocol with development inputs | [Host inputs and setup selection](inputs.md) |
| Understand role runners, messages, resource views and cancellation | [Interactive execution](../compiler/interactive-execution.md) |
| Produce a proof and validate it without a live prover | [Artifact execution](../compiler/artifact-execution.md) |
| Implement an artifact reader or writer | [Concrete artifact format](../compiler/artifact-format.md) |
| Understand source and construction identity | [Artifact identity](artifact-identity.md) |
| Understand loading, backend contracts and progress assumptions | [Runtime design](design.md) |
| Connect native values and complete results to logical meaning | [Realization guide](../guides/realization.md) |
| Run the finite direct/table reference route | [Reference execution](reference-execution.md) |
| Select the public-operand Ristretto kernel | [Public MSM](public-msm.md) |

The [runtime crate](../../crates/zkc-runtime/README.md) owns the execution API;
[backend admission](../../crates/zkc-backends/README.md) binds concrete inputs
and setup; the [Arkworks adapter](../../crates/zkc-arkworks/README.md) describes
its implementations. [Tools](../../crates/zkc-tools/README.md) expose complete
jobs rather than a cross-language analysis loop.

The finite direct/table route has independent consumers and proof support. It
is a reference profile alongside the interactive native pipeline, not a required
intermediate step for every protocol. Concrete format versions have their own
admission rules; version numbering does not imply compatibility with older tags.

Construction, input decoding and execution can fail at different boundaries.
Retained effects and consumed resources follow the relevant complete-result
contract. A trusted cryptographic library still needs correct input, domain,
setup and implementation binding; its use alone does not prove those connections.
