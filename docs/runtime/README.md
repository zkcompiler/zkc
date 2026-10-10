# Runtime and Hosts

The Rust Runner executes `zkc.program/0` using installed kernels. Hosts
authenticate artifacts, prepare inputs and setup, manage resources and limits,
and report or publish complete results. Entry, proof and joint execution share
this Runner.

| Task | Reference |
|---|---|
| Compile and invoke a named source Entry | [Entry guide](entries.md) |
| Integrate proving and verification | [Proof execution](proofs.md) |
| Authorize bounded retries | [Attempts](attempts.md) |
| Run direct Protocol IR | [Bundle walkthrough](bundles.md) |
| Understand authority and failure handling | [Runtime design](design.md), [artifact identity](artifact-identity.md) |
| Configure operational ceilings | [Capacity contract](../spec/runtime/capacity.md) |
| Check exact admission, frames and publication | [Specification](../spec/README.md#native-contracts) |

The [runtime crate](../../crates/zkc-runtime/README.md) owns the interpreter and custody
API; [backends](../../crates/zkc-backends/README.md) own installed bindings;
[tools](../../crates/zkc-tools/README.md) own Host APIs and commands. The
[representation laws](../spec/realization/representations.md) state the
obligations of a native realization. Existing independent Lean models do not
prove this Runner correct; see [assurance](../assurance.md).
