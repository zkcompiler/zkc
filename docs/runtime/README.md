# Runtime and Hosts

The Rust Runner executes `zkc.program/0` using installed kernels. Hosts
authenticate artifacts, prepare inputs and setup, manage resources and limits,
and report or publish complete results. Entry, proof and joint execution share
this Runner.

`run`, `prove`, `verify` and their `bundle` forms accept `--threads=COUNT`
with `1..=256` CPU workers (default: 1). Source commands also accept it with
`--dry-run`, which validates inputs without numerical execution. One command
shares one context across numerical work, participants and reached child
deployments. Reports include `cpu.workers`, and human output shows `CPU workers`.
SDK applications pass `zkc::execution::CpuExecution` to `admit_with_cpu` before
any backend or child admission. Each default admission creates one fresh owned
serial context; explicit clones share a context across independent Hosts.
`with_cpu` can rebind an idle admitted Host. See the
[SDK CPU API](../../crates/zkc/README.md#cpu-execution) for construction and sharing.
The ceiling covers only the context's numerical workers. Caller validation,
imports and partial effects stay ordered on the caller, while numerical leaves
use the supplied pool. Dropping the last owner requests Rayon worker shutdown
without a guarantee that worker threads have joined.
CPU policy does not change artifact identity, authority, resource budgets or
failure handling, and worker selection does not use Rayon environment variables.

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
API; [mathematical kernels](../../crates/zkc-kernels/README.md) own typed
arithmetic without VM authority; [native backend](../../crates/zkc-native/README.md) owns installed bindings;
[SDK](../../crates/zkc/README.md) owns application Host APIs; the separate
[CLI](../../crates/zkc-cli/README.md) owns arguments, commands and presentation. The
[representation laws](../spec/realization/representations.md) state the
obligations of a native realization. Existing independent Lean models do not
prove this Runner correct; see [assurance](../assurance.md).
