# Runtime and artifact design

The [protocol pipeline](../compiler/protocol-pipeline.md#4-participant-meaning-and-execution)
adds independent role runners and explicitly selected drivers to these custody
responsibilities. An enclosing experiment session, an independent role's live
execution and the current finite native `Session` are distinct scopes. The
illustrative whole-experiment API below does not require every participant to
own its peer or a live joint controller.

The
[representation specification](../spec/realization/representations.md),
[codec specification](../spec/realization/codecs.md) and
[binding specification](../spec/realization/artifacts.md) own meaning; this chapter chooses Rust APIs
and deployment boundaries. The [finite table implementation](../compiler/table-execution.md)
provides plan admission, owned storage and synchronous execution with bounded
differential evidence. The [native runtime guide](reference-execution.md) describes the maintained invocation
lifecycle. The enclosing experiment controller, general endpoint admission and
broader native correspondence remain work; selected physical optimizations and
artifact execution already exist at the scopes in [status](../status.md).
The [representation design](../compiler/representation.md) treats existing
native APIs as behavioral evidence. Final production APIs follow the physical-plan
and target decisions in the [roadmap](../roadmap.md).

## 1. Ownership and deployment

The compiler chooses the plan. The runtime loads an admitted immutable plan and
executes its selected coarse operations. It does not repeat demand analysis,
search, scheduling, fusion or protocol selection. Useful kernels process arrays,
folds, FFTs, MSMs or pairing products; avoid interpreter dispatch for every scalar
multiplication.

The public API will distinguish an immutable admitted program from an owned
session. A session owns the live world, cursor, provider/tape state, buffers,
immutable preparation cache and any continuation ledger. The admitted-program
constructor is private to checked admission. Shared program bytes may use `Arc`;
shared mutable session state is not the default design. The separation resembles
the context-bound ownership of a Wasmtime store, but zkc must validate foreign
handles and return its specified error rather than copy an unrelated API's panic
behavior. [Wasmtime Store](https://docs.wasmtime.dev/api/wasmtime/struct.Store.html).

Illustrative API, not a promised release surface:

```rust
Runtime<B>::admit(artifact, policy) -> Result<AdmittedProgram<B>, AdmissionError>
Runtime<B>::start(program, inputs, providers) -> Result<Session<B>, StartFailure<B>>
Session<B>::execute(self, control) -> RunReport<B>
```

Here a `Session` owns the **whole enclosing experiment**, including its permitted
controller and local attempts. A local attempt can stop while the explicit
session-result wrapper returns data to that enclosing controller. The same
private session retains the advanced tape, world and consumed ledger for the next
attempt. This neither catches arbitrary outer stops nor resumes a stopped suffix.
An outer stop ends the enclosing experiment. The initial API does not export a
restartable snapshot or reconstruct provider state from a public report.

This is the target lifecycle. The current Rust `Session` in
[`execution.rs`](../../crates/zkc-runtime/src/execution.rs) represents one owned
invocation and returns `Completed` with residual bindings. It is not already the
whole enclosing controller. The production API must distinguish these lifetimes
and preserve the binding state when implementing repeated permitted attempts.

`start` validates without draws, cursor consumption, ledger changes or installation.
If validation fails, `StartFailure` returns ownership of the unmodified inputs
and providers along with its error; moving them into the API must not destroy
custody on `Err`. Setup that can mutate state is an execution operation with a
complete outcome, not a hidden side effect of successful admission/start.

Admission errors precede execution. An operation's recoverable error belongs in
its returned reply. Terminal reject, abort, exhaustion, incompleteness and refusal
remain distinct complete outcomes. `RunReport` distinguishes a completed modeled
execution from a host interruption for which no complete correspondence is
available. A completed record retains residual state and events privately; an
observer projection exposes only the declared view. A failed call is never
implicitly rolled back. Rust's `?` is appropriate only where it implements the
specified error layer.

The table runtime preserves completed outcomes and residual bindings. That
invocation result does not establish the full controller lifecycle,
arbitrary allocation success or a native extraction theorem. Internal access to
residual state is separate from an authorized public observation API.

## 2. Values and backend contracts

Use static backend-associated scalar/group/buffer types in kernel loops. Runtime
backend selection, if required, chooses a typed session through an outer enum or
coarse dispatch. A universal boxed field value and a dynamic call per scalar
operation add costs and make representation reasoning harder without a current
need. This is an engineering judgment, not a measured speedup.

Keep algebra kernels, codecs and providers as distinct interfaces. A generic
backend contract states mathematical domain, operation behavior, shapes, alias
rules, failures and observations. Registration binds the actual adapter/build to
that contract under either evidence or explicit trust. A Rust trait implementation
alone establishes no field identity, codec correctness or probabilistic law.
Changing conforming backends reuses compiler laws; it changes the representation
and implementation-contract instance that must be supplied.

Implement these separate kernel/codec/provider contracts in the first runtime,
not after a concrete backend has spread through the dispatcher. Logical value
and domain identities stay independent of pointers and the selected field
library. Slot descriptors and backend-owned buffers state shape, layout,
ownership, alias permissions and capacity behavior. The dispatcher uses their
operations rather than accessing every value as a host `Vec` or raw pointer.
This is a typed boundary with one working adapter, not a requirement for dynamic
dispatch per scalar or a general device-memory framework.

A focused runtime contract test must substitute a distinct storage or provider
test adapter without editing the dispatcher. This exercises the actual boundary
alongside the production adapter; it is not a second production backend or a
proof that arbitrary providers satisfy their contracts.

The finite table runtime now implements this storage boundary with
`BufferStore<T>` and two layouts: packed buffers and retained reservation
segments. A successful reservation permits immutable publication without new
payload/descriptor allocation. Reads borrow from the owner; later reservation
cannot run while that borrow is live. Both stores preserve previously published
contents and reject foreign references. The consumer selects a statically typed
session; no per-scalar dynamic dispatch is introduced. The current table adapter
uses `u8` for its finite F₂/F₇ profile; the generic buffer type is not a claim
of general field or
device support. Backend lawfulness remains an explicit obligation: valid
handles alone cannot detect a well-shaped but incorrect payload.

Extending this finite table interpretation to another field must close the gap between
the selected backend-associated types. The generic `Bindings::Value` and
`BufferStore<T>` boundaries are available, but `TableBindings`, its values,
events, scratch storage and codecs still select `u8`. The C++ table library and
Lean example decoder also restrict domains to F₂/F₇. A scalar-kernel trait alone
does not make this whole path ready for a different field.

Other execution routes already use real backends: the
[backend crate](../../crates/zkc-backends/README.md) supplies selected Arkworks,
Dalek and Plonky3 operations. Those installations do not widen the F₂/F₇ table
profile by themselves. Extending that profile requires a joined source,
checker, table representation and native adapter, with the coverage recorded in
[status](../status.md). Select upstream APIs from the actual pinned dependency
and consumer, and keep borrowed/in-place operations compatible with immutable
published values.

Preserve concrete field types within kernel loops. Keep mathematical domain and
canonical codecs separate from backend storage representation. An upstream
in-place operation needs an exclusively owned work buffer or an accounted copy;
it cannot mutate a published immutable source table with live aliases. Check
upstream shape preconditions before invocation and retain the logical failure
behavior. Expose coarse evaluation and restriction operations so an adapter can
use existing vectorized or parallel routines. zkc owns the selected plan and any
required glue or new scheduling algorithm; upstream implementations supply the
existing arithmetic and polynomial kernels that fit their declared contracts.
Validate the first source through MLIR, the corresponding Lean interpretation
and native execution before treating this boundary as delivered. Backend
implementation laws may remain explicit trust; adapter correspondence still
requires differential and boundary controls.

The initial kernel interface completes synchronously: on every modeled return
or stop, accesses to supplied buffers have finished and declared ownership can
be recovered. An interrupted call does not establish that fact. These completion
and ownership conditions are part of the contract now; future device kernels
can implement the same synchronous boundary by waiting for completion. Overlap,
reentrant callbacks and finer controller intervention require additional
contracts before the runtime may expose them.

Internal IDs use separate newtypes for program, instance, domain, slot and
resource. Buffers carry a session identity and generation or an equally strong
ownership construction. Bounds, lifetime, same-slot reuse and aliases are checked
where handles enter an operation. Byte encodings and buffer shapes are not Rust
enum layouts. Keep unsafe/FFI/device code at explicit adapter boundaries; the
owned core forbids unsafe code.
[Rust API guidelines](https://rust-lang.github.io/api-guidelines/checklist.html).

The representation theorem must interpret returned handles in their **actual
post-state**. The new Lean `Execution.Relates` supports different source/native
reply types, related residual states and equal projected ordered events. Its
sequencing law requires each continuation to preserve that relation; its
composition law shares the intermediate value and state witness. This is a
general mathematical connection target, not a theorem about this Rust crate.
[Implemented relation](../../formal/Zkc/Realization/Simulation.lean).

## 3. Artifact and checking boundary

The [target design](../compiler/targets.md) selects a physical native plan and
a verifier-acceptance relation as separate consumers of retained logical meaning.
They share bounded envelope/metadata mechanics. Body codecs, input mappings and
semantic checking judgments remain target-specific; a common JSON schema is not
a common interpreter or a proof of correspondence.

The build driver retains the original source, public specialization and requested
policy before invoking the compiler. Whole-job exchange has this shape:

```text
CompileRequest -> CandidateBundle
(original, candidate, policy) -> CheckResult
(accepted conclusion, exact plan, implementation requirements) -> DeploymentArtifact
DeploymentArtifact + installed backend policy -> AdmittedProgram
```

Define finite source, plan and certificate schemas beside their semantic
interpretations. Choose a strict versioned encoding for the first joined slice:
fixed constructor tags, explicit lengths, canonical naturals/field encodings,
ordered bindings, bounded nesting and mandatory full-input consumption. Reject
duplicate declarations, unknown mandatory constructors and unresolved references.
JSON can serve diagnostic fixtures; it does not determine canonical identity.
The exact binary tag table is an implementation deliverable, not an invented
layout to freeze before there is a decoder.

The first schema nevertheless separates format version, required capabilities,
semantic/rule dependencies, selected claim and realization kind. The first
implemented kind is Plan execution. A future generated-code kind must bind its
own correspondence and entry interface, rather than being relabeled as a checked
Plan. Unknown required capabilities or semantic versions are rejected; reserved
extension space is never implicitly executable. Evidence dependencies and cost
or diagnostic metadata are separate, so adding a measurement does not silently
change a proof's subject. These are required schema fields and relationships,
not a claim of a stable public binary ABI or an implemented alternate loader.

Source identity, specialized captures, public instance, observer/relation,
contract versions, final plan and proof dependencies must all be bound. Check
against the driver's retained input, not only the producer's copy. An immutable
admitted object owns both the checked bytes and their decoded plan; execution
does not reopen an arbitrary path after checking. Hashes support lookup/integrity
under a stated policy, not mathematical truth or authority to publish secret
capture fingerprints.

Admission policy includes the consumer's expected subject and public instance.
A different internally valid proof bundle must still fail that selection.

Separate the compiled subject from an invocation. Compilation binds public
specialization, ordered input/capture declarations, role, semantic contracts and
the permitted observer/relation. Evidence quantifies over allowed runtime values.
`start` binds actual private values and providers to those declarations without
putting them in compilation artifacts. An immutable runtime capture is frozen
for its declared lifetime; it is not automatically a compile-time constant.
The first implementation specializes only on public data. Secret-dependent
specialization and cross-session preparation caches require their own disclosure
and lifetime argument before introduction.

The loader checks each retained requirement against the requested policy.
Evidence may discharge it, policy may explicitly trust its implementation
contract, or a justified guard may establish it at the corresponding source
point. Source guards stay in their original execution position unless a law
justifies moving them. A provider distribution law cannot be discharged by an
ordinary runtime value check. An unresolved conditional checking result remains
inspectable, but does not construct an `AdmittedProgram` unless every requirement
has an allowed disposition, including the placement of dynamic guards.

Distinguish three policies: kernel-replayed proof; a trusted native checker
execution under an explicit build assumption; experimental execution without that
claim. A naked `verified: true` field represents none of them. Keep unresolved
requirements and unsupported/inconclusive outcomes visible. A semantic proof can
survive a cost-model update while its performance ranking does not; a changed
failure contract invalidates affected proof evidence.

The typed checker request/response contract belongs in `zkc-runtime` admission;
`zkc-tools` maps subprocess, timeout and parsing outcomes into it. Compiler
evidence and runtime invocation results use separate types.

Checker responses preserve useful distinctions: accepted with resolved
requirements, conditional evidence with unresolved requirements, unsupported
profile/rule, malformed response/artifact, exhausted checking budget, I/O failure,
and a refutation only when its evidence establishes one. These are response
categories for the production consumer, not new protocol stop constructors.
The current finite consumer safely refuses several of them as `unchecked-plan`;
it does not establish semantic falsehood. Exact wire tags move with its consumer.

Composing evidence requires the same actual intermediate subject and compatible
input/value/state/observation mappings. Requirements retain their types and
subject bindings; merging string names or matching theorem labels is insufficient.
A changed candidate requires fresh applicable evidence even when cached compiler
analyses remain valid. The admitted object retains the checked body and bytes
through execution, including backend selection under the accepted policy.

## 4. Randomness, cancellation and resource failure

Initialize a provider from the named **joint** law and retain its evolving state.

An external experiment controller may retain these providers across owned
invocations. The core runtime need not prescribe a universal controller object.
Storage ownership, invocation identity and security-experiment identity have
different lifetimes: immutable aliases can survive a call while provider resets,
retries and fresh response resources require their own selected contract.

Do not construct independence by calling an RNG separately for each logical
operation. Failed attempts retain consumed tape and initialization probability;
discarding failure runs changes the experiment. Replay records must have a
declared observation policy because transcripts and seeds can contain secrets.

Start with synchronous sessions. Cancellation is observed only at specified
operation boundaries and preserves the completed prefix. A future async wrapper
can move a whole owned session to a worker; dropping its future does not establish
rollback or device cancellation. Device work must be fenced before buffers can
be reused. Reaction between two emissions inside an atomic call needs a different
operation boundary and corresponding semantics.

Keep permitted observation, provider initialization and completion boundaries
explicit in the first session interface. Even with one provider, do not bake in
fresh-independent sampling or equate host task scheduling with protocol steps.
A later wrapper may schedule a whole owned synchronous session without changing
its internal atomicity. A genuinely interleaved protocol needs a separately
supported execution scope and evidence; an `async` flag is not that extension.

Logical exhaustion and host allocator/device/process failure are distinct. The
first has a modeled complete result; the latter may yield no recoverable complete
state. Establish capacity/progress premises or implement and relate recoverable
allocation explicitly. Neither Rust memory safety nor a successful finite run
proves this obligation. Internal event accumulation also allocates; a later event
sink optimization requires its own observation correspondence.

For the first native path, use a public capacity plan for zkc-owned slots,
scratch buffers and retained events. Derive checked size/range bounds and
reserve the required storage before modeled execution where possible. The
compiler proposes the capacity/layout plan; the consumer checks its bounds
against the actual public inputs. Independent bound validation is permitted
runtime admission work, not a second optimization or scheduling engine. Failure
to establish that capacity is a start failure returning unchanged inputs and
providers; it is not a new protocol rejection. Backend-internal allocation and
progress remain explicit implementation assumptions until covered. This is a
conditional realization domain, not a claim to preserve admission on every host.

Logical tape/resource exhaustion and source-defined allocation failures still
occur at their specified execution points. A preparation optimization may use
the admitted scratch capacity; it cannot silently introduce a new logical stop
or erase an existing one. Private-dependent use within an admitted public bound
can remain dynamic; the reservation does not specialize on private values. If
no public reservation bound can be justified, retain a supported direct route
or report the configuration unsupported under this first policy. A richer
dynamic allocator needs a related failure contract before replacing this policy.

## 5. Packages, native proof and acceptance

Start with `zkc-runtime`; add `zkc-tools` for the SDK and CLI when whole-job
admission is implemented. Keep internal format, session, value and backend
interfaces as modules. Split a backend adapter when it introduces independently
selectable dependencies; split a shared format crate when two real Rust consumers
need it without runtime dependencies. This avoids empty crates while preserving
the independence the interfaces need.

CMake builds the compiler separately. A runtime `build.rs` must not build MLIR,
download Lean or run an optimizer. Cargo workspaces share lock/feature resolution;
`default-members` alone is not dependency isolation. Extractor experiments with
incompatible toolchains live in separate workspaces.
[Cargo workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html).

The [default assurance policy](../assurance.md#6-implementation-correspondence-policy)
requires differential validation of each delivered native slice against executable
Lean meaning, including residual state and failure behavior under an explicit
relation. It does not require a native proof before delivery.

If a native proof is pursued, its first target is the **actual** owned dispatcher,
buffer/key validation and complete-outcome plumbing used by execution. Assess Aeneas first
on those functions, with hax as a concrete alternative. Pin frontend, extractor,
Rust, Lean, source features and external models. Regenerate definitions and prove
their relation to `Execution.Relates`, including panics and required progress.
Do not prove a rewritten neighboring program while shipping another one. Neither
tool has been exercised here; upstream supports a restricted Rust subset and
requires models for some external definitions.
[Aeneas](https://github.com/AeneasVerif/aeneas),
[hax Lean guide](https://hax.cryspen.com/manual/lean/quick_start/).

Acceptance includes a minimal consuming application with no compiler/prover
installation; same-typed capture and artifact substitution controls; failed-write
and exhausted-tape residual state; stale/foreign handles; codec partial input;
failure to install without cache population; two local attempts with residual tape
and consumed failed-arm custody; failed start returning unchanged owned inputs;
and two materially different clients
using the same preparation contract. Measure dispatch, kernel work, memory, wire
bytes, compilation and proof replay separately against the same algorithm/backend.
No performance advantage is claimed by the present foundation or probes.
