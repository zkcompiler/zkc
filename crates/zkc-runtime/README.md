# Native program runtime

`zkc-runtime` admits and executes `zkc.program/0`, the physical program produced
by the compiler. `vm::Program` owns the exact admitted
bytes and the derived typed program. `interpreter::Runner` executes one role
with caller-supplied values and an independently installed backend. The VM
instance owns frames, resource accounting and installed calls; the interpreter
owns control flow and value environments. See the
[VM contract](../../docs/spec/runtime/vm.md).

`Program::decode(bytes, &contracts)` checks exact records, nominal physical types, operation
bindings, SSA, local control, bounded value-counted loops, message data, affine resources and
service interfaces without a backend. `Program::check_installation` optionally
checks deployment availability. Loading links an independently owned backend,
selects an entry and role and enters its resource frame. Execution proceeds through explicit local, query, send, receive and
control boundaries. A stopped runner retains its diagnostics and completed
resource transitions; cancellation closes its active frames.

`vm::Contracts` is an immutable trusted admission context retained by the Program.
`Contracts::standard(policy)` explicitly contributes the existing standard Native
inventory. `ContractsBuilder::empty()` contributes only VM control types;
`ContractsBuilder::standard()` also contributes the standard inventory. Builders
can add mathematical representations, aggregate storage rules, exact implementations
and bounded aggregate implementation families in the existing inventory, then
freeze with an explicit `ExecutionPolicy`. Artifact
names cannot contribute an installation or authorize timing premises.

Extension identities contain catalog-scoped slots. Clone the frozen context to
share its identity with a backend; `with_policy` preserves the inventory and IDs
while selecting another immutable trusted policy. Rebuilding a catalog creates
distinct extension IDs. `contracts.physical_type` parses contributed layouts;
`PhysicalType::parse` and the `OperationBinding` convenience queries inspect the
fixed standard contracts only. One representation name can implement several
explicit logical types. A direct `representation.convert` implementation must
contribute the exact ordered physical ports; no default conversion is installed.
Extension representations have no implicit message codec permission.

`PhysicalType` retains complete ordered physical children separately from its
logical schema. Child layout brackets are omitted only when every child has its
standard default layout; explicitly listing those defaults is noncanonical.
`sequence_element`, `field_array_element`, `fixed_vector_element` and
`variant_payload` read stored children. Variant packing and unpacking carry the
complete `PhysicalType`, including inactive alternatives.

Executable binding rows contain five fields:
`[name, contract, logical_arguments, implementation, physical_arguments]`.
Aggregate families select one complete container argument; `[]` explicitly
chooses the canonical default container. Direct conversion uses logical arguments
`[logical]` and physical arguments `[source, target]`. Only an installed exact
ordered pair permits conversion; no aggregate conversion is inferred from a leaf.

`add_wire_permission` grants an exact layout and codec. Standard catalogs own the
generic sequence and variant Native frames; empty catalogs need an exact parent
grant or an explicitly contributed aggregate frame family. A contributed storage
owner uses `allow_aggregate_native_message`. Every selected child needs permission,
including inactive alternatives, and actual backend support is independently
checked. Fixed vectors remain local data. Immutable preparation eligibility is
independent of wire permission and always requires ordinary backend validation.

`ExecutionPolicy::operand_independent()` accepts only implementations whose
trusted owner supplies that timing premise. `general_purpose()` explicitly
permits both unspecified and variable timing. Neither policy establishes a
whole-program timing guarantee. Deterministic preparation is a separate promise.

`vm::Backend::Operation` implements `vm::InstalledOperation`: an immutable
installed handle for one exact binding. `vm::OperationSignature` describes its
ports and attribute rules; `vm::BoundSignature` specializes those ports to
physical types. Extension handles independently supply `implementation_id` and
`requirements` as well as actual ports. Linking compares all three against the
admitted context and checks its timing policy before entering a frame. Operations
include effects and partial failures. Installation
does not grant resource authority or establish numerical purity; the backend
checks live custody and policy at each invocation.

`vm::ProgramRole` exposes a static layout and `ProgramState` exposes
non-advancing observations. The application host chooses scheduling and transport.
`NativeProofEntry` checks the restrictions of the current native proof policy.
`host::joint` owns bundle admission, ordered scheduling and bounded reports;
its `Bundle::admit` and `admit_pinned` take the same explicit contract context;
`host::proof` owns producer/validator execution and cancellation; `host::wire`
owns bounded framing and the `WireBackend`/`ProofBackend` contracts. These consume
Runner actions without changing VM or interpreter semantics.

A trusted adapter supplies complete-type wire support, size bounds, encode/decode,
raw byte access and Boolean projection. Missing measurement refuses before
decoding. Invalid receives complete with Decode; capacity and adapter failures
remain Host failures. Native implements the closed native profile in its own
crate. Runtime depends on neither native nor kernels. Application Hosts in
`zkc` retain package/deployment identity, setup and public-input authority,
acceptance selectors, prepared computation policy and publication.

Shared-ledger reports retain live storage guards. `Produced::into_parts()`
transfers proof bytes, outputs and proof-buffer reservations to the application;
keep the reservations while retaining the buffer. Runner output custody still
uses `into_retained_outputs()`. Dropping guards releases only live capacity,
never cumulative work or allocation charges.

Protocol algorithms are source libraries; field arithmetic and cryptographic
operations are supplied by installed backends. The runtime hashes canonical
relation carriers for identity, independently of backend operation installation.
`Bundle::table_widths` derives immutable element widths after whole-table
carrier admission, without a height. `Bundle::polynomial_view` checks static
carrier compatibility; its height-taking methods check actual domain, policy,
windows and limits when called. Point substitution requires no domain.
Admission establishes executable structure, not compiler correctness or protocol
security. See [the VM module guide](src/vm/README.md).

Canonical logical trees, occurrence descriptors and lazy proof framing live in
[`zkc-format`](../zkc-format/README.md); runtime consumers add admission and
resource authority. Other runtime helpers:

- `attempt` and `iteration`: bounded generic retry and iteration controllers.
- `ring`: typed ring-arena admission and degree/read analysis.
- `relation`: deterministic multi-table and staged relation carriers, admission
  and bounded reference evaluation through caller-supplied field arithmetic.
  These are library APIs; they are not Runner instructions or proof checkers.

Run the crate's tests with `cargo test -p zkc-runtime`. The runtime-only
`tests/host.rs` consumer exercises both drivers with an independent backend,
Value and wire implementation. Native integration tests exercise the same
interfaces with native values and cryptographic kernels.
`tests/admission_contracts.rs` contributes an independent non-curve physical
representation, executes adjacent mathematical calls through LocalRunner and
Runner, and transports the Boolean result through the shared joint Host. Its
negative controls cover forged names, physical erasure, duplicate owners,
foreign catalog IDs, actual-port drift, missing handlers and timing permission.
`tests/aggregate_layouts.rs` independently contributes noncurve scalar/vector and
fixed-vector storage, then exercises selected sequences and variants through
Runner, shared Host, branch/loop control and cold/warm preparation. It covers
complete descriptor bounds, inactive layout identity, malformed values, stale
resource handles and recursive wire authorization.
