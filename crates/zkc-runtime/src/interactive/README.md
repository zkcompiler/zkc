# Native interpreter

`admit_supplied` accepts exactly `zkc.program/0`. It validates all retained
functions, participant bodies, entries and operation declarations before asking
the backend to confirm installed signatures. `Admitted` retains the exact bytes
and immutable typed model. Artifact text cannot install backend code.

An entry maps roles to flat participant definitions. Participants contain local
calls, service queries, messages, bounded value-counted loops and returns.
Participant arguments and loop operands are explicit. Admission rejects
participant calls, source family selectors and loading-time programs.
Local functions support typed arithmetic operations and structured control,
including conditionals, bounded iteration, variants, storage release and stops.

`Runner::new_with_budgets` validates actual entry operands and establishes the
entry frame. Each child frame receives only its explicit operand view. Affine
values cannot be copied, borrowed ancestor values cannot escape their admitted
view, and service custody follows the selected entry interface. Backends own
capability issuance, state transitions and cryptographic operations.

`poll` exposes the next action; `poll_ref` and `program_state` support borrowed
inspection. Hosts cross local computation, service, send and receive boundaries
explicitly. `advance_local_control` crosses native control boundaries. A static
`program_entry` layout lists each loop body once, independently of its invocation
count. It is descriptive data and cannot replace the admitted executable.

`deliver` checks a typed packet's envelope and payload. `complete_receive` accepts
a result from a host's native wire decoder, retaining decode failures as stops.
Both APIs preserve role, session, entry and dynamic occurrence separation.
A rejected cut does not advance the role. Cancellation and failure close frames
in reverse entry order; completed backend effects are never rolled back.

Value retention, instruction work, iterations and stack depth have independent
limits. Loading failures return backend custody. A stopped or completed runner
cannot be reused as a fresh proof execution. Inspection does not consume values.

`operations/` assembles independently authored logical contracts and physical
selection policies. Family owners validate nominal domains, providers and
payload restrictions; `operations/support.rs` holds shared construction helpers.
The backend separately advertises and executes the matching signatures.
`logical` supplies canonical transcript trees; explicit native transcript
origins are independent of executor frame names.

`NativeProofEntry::new` validates the current native proof rules, including
structured data, public iteration, commitments and authored transcript transitions. The host authenticates
its deployment and public inputs and independently interprets the verifier's
Boolean result. These structural checks are not a security theorem.

Unit tests exercise exact admission, explicit control, resource cleanup, message
framing boundaries and malformed inputs with mock backends. `zkc-backends` and
`zkc-tools` provide tests with native cryptographic values, services and hosts.
