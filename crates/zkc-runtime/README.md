# Native program runtime

`zkc-runtime` admits and executes `zkc.program/0`, the physical program produced
by the compiler. `vm::Program` owns the exact admitted
bytes and the derived typed program. `interpreter::Runner` executes one role
with caller-supplied values and an independently installed backend. The VM
instance owns frames, resource accounting and installed calls; the interpreter
owns control flow and value environments. See the
[VM contract](../../docs/spec/runtime/vm.md).

`Program::decode` checks exact records, nominal physical types, operation
bindings, SSA, local control, bounded value-counted loops, message data, affine resources and
service interfaces without a backend. `Program::check_installation` optionally
checks deployment availability. Loading links an independently owned backend,
selects an entry and role and enters its resource frame. Execution proceeds through explicit local, query, send, receive and
control boundaries. A stopped runner retains its diagnostics and completed
resource transitions; cancellation closes its active frames.

`vm::ProgramRole` exposes a static layout and `ProgramState` exposes
non-advancing observations. The application host chooses scheduling and transport.
`NativeProofEntry` checks the restrictions of the current native proof policy;
proof framing and application acceptance belong to `zkc-tools`.

Protocol algorithms are source libraries; field arithmetic and cryptographic
operations are supplied by installed backends. The runtime hashes canonical
relation carriers for identity, independently of backend operation installation.
`Bundle::table_widths` derives immutable element widths after whole-table
carrier admission, without a height. `Bundle::polynomial_view` checks static
carrier compatibility; its height-taking methods check actual domain, policy,
windows and limits when called. Point substitution requires no domain.
Admission establishes executable structure, not compiler correctness or protocol
security. See [the VM module guide](src/vm/README.md).

General helpers retain separate owners:

- `attempt` and `iteration`: bounded generic retry and iteration controllers.
- `logical`: canonical trees and domain-separated transcript occurrences.
- `ring`: typed ring-arena admission and degree/read analysis.
- `relation`: deterministic multi-table and staged relation carriers, admission
  and bounded reference evaluation through caller-supplied field arithmetic.
  These are library APIs; they are not Runner instructions or proof checkers.

Run the crate's tests with `cargo test -p zkc-runtime`. Backend and host tests
exercise the same interfaces with actual native values and cryptographic kernels.
