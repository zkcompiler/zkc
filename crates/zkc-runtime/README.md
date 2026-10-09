# Native program runtime

`zkc-runtime` admits and executes `zkc.program/2`, the physical program produced
by the mathematical compiler. `interactive::Admitted` owns the exact admitted
bytes and the derived typed program. `interactive::Runner` executes one role
with caller-supplied values and an independently installed backend.

Admission checks exact records, nominal physical types, operation bindings, SSA,
local control, bounded value-counted loops, message data, affine resources and
service interfaces. Loading selects an entry and role and enters its resource
frame. Execution proceeds through explicit local, query, send, receive and
control boundaries. A stopped runner retains its diagnostics and completed
resource transitions; cancellation closes its active frames.

`interactive::ProgramRole` exposes a static layout and `ProgramState` exposes
non-advancing observations. The application host chooses scheduling and transport.
`NativeProofEntry` checks the restrictions of the current native proof policy;
proof framing and application acceptance belong to `zkc-tools`.

The runtime contains no cryptography or protocol-specific algorithm. Backend
operation installation is independent of the runtime's type/binding resolver.
Admission establishes executable structure, not compiler correctness or protocol
security. See [the interpreter contract](src/interactive/README.md).

General helpers retain separate owners:

- `attempt` and `iteration`: bounded generic retry and iteration controllers.
- `logical`: canonical trees and domain-separated transcript occurrences.

Run the crate's tests with `cargo test -p zkc-runtime`. Backend and host tests
exercise the same interfaces with actual native values and cryptographic kernels.
