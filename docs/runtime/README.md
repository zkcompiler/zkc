# Runtime and Hosts

The Rust Runner executes `zkc.program/1` using installed kernels. Hosts add the
application boundary: authenticate an artifact, prepare inputs and setup, manage
resources and limits, then report or publish the result. Entry, proof and joint
execution share this Runner.

| Task | Reference |
|---|---|
| Compile and invoke a named source Entry | [Entry execution](../language/entries.md) |
| Execute direct mathematical MLIR | [Bundle and proof walkthroughs](bundles.md) |
| Understand authority and failure handling | [Runtime design](design.md) |
| Bind packages, deployments and invocation context | [Exact artifact identity](artifact-identity.md) |
| Produce and independently validate proofs | [Native proof compilation](../compiler/native-proofs.md) |
| Relate execution to a mathematical model | [Realization guide](../guides/realization.md) |

The [runtime crate](../../crates/zkc-runtime/README.md) owns the interpreter and
custody API, [backends](../../crates/zkc-backends/README.md) own installed bindings,
and [tools](../../crates/zkc-tools/README.md) own Host APIs and commands. Exact
[program](../spec/profiles/compiler/program.md), [bundle](../spec/profiles/compiler/run.md)
and [proof](../spec/profiles/compiler/native-proofs.md) contracts have separate
admission rules while sharing the executable format.
