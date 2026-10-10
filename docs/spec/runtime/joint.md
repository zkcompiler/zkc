# Joint execution bundles

This profile runs the fixed role roster of one
[program entry](../formats/program.md) in an explicitly supplied
order. The compiler derives that order from a mathematical protocol's verified
projection metadata. Runtime admission checks the candidate and dispatch plan;
it does not independently establish correspondence to source.

## Compiler ownership

`compileRun(text, filename, options, registry)` accepts mathematical
MLIR in the `protocol` profile. It owns the context, runs prepare, projection,
optional participant simplification, math lowering and physical selection, then
exports the typed physical participant carrier. Adjacent-stage preservation
checks retain action order, calculation origins, statement interfaces and result
maps. The API returns an owned final `Compilation` and a complete bundle. The
compilation owns its MLIR context, module and statistics. Failures are owned
`CompilationError` values; no partial bundle is returned.

The command writes exactly the returned bundle bytes, without an added newline.
An application pin for this artifact therefore also names the compiler's exact
returned string. The command is:

```sh
zkc-compile protocol-bundle protocol.mlir --entry=main
```

`--no-simplify` disables participant simplification; protocol preparation still
runs. `--release-storage` selects local storage release during physical lowering.
Neither option changes the exposed participant instruction sequence. Mathematical
MLIR input is bounded to 16 MiB with nesting at most 64. Entry and filename strings
are bounded to 4096 bytes. The default entry is `main`.

The producer resolves each retained `(participant, site, operation)` against the
exported typed carrier. Instruction indices count actual emitted carrier body
instructions, including return. Guard recipes belong to their source action even
though they also have calculation origins. Other generated calculations precede
the demanding action, or precede that role's return. Generated-looking names have
no special meaning. The final module owns retained statement information; the
bundle carries executable scheduling data. It adds no IR stage or dialect.

## Bundle and admission

`zkc.run/0` is one JSON object with exactly these mandatory fields:

```json
{
  "format": "zkc.run/0",
  "candidate": "<exact zkc.program/0 JSON text>",
  "entry": "main",
  "roles": ["Alice", "Bob"],
  "steps": [
    {"role": 0, "instruction": 0, "anchor": 0},
    {"role": 1, "instruction": 0, "anchor": 0},
    {"role": 0, "instruction": 1, "anchor": null},
    {"role": 1, "instruction": 1, "anchor": null}
  ]
}
```

This illustrative plan fits a direct send/receive followed by both returns.
Role and instruction indices are nonnegative integers; `anchor` is a mandatory
nonnegative integer or null. Unknown or duplicate fields, floats, negative
indices, missing fields and trailing JSON are refused. The candidate remains an
exact embedded string, with no file resolution or sidecar. Runtime owns its
positional decoding, static typing, installed-kernel admission and immutable
custody. `Admitted::program_entry` supplies the action layout and resolved send
operand types; Tools does not decode participant instructions separately.

Installed ceilings and defaults are 16 MiB outer bytes, 4 MiB decoded candidate bytes, 1024 roles,
32768 static dispatch steps including returns, outer nesting 256, 250000 outer JSON nodes,
and 4096 decoded UTF-8 bytes per ordinary string. A host may lower these through
`BundleLimits`; higher requests refuse with `BundleError::Limit`. Byte/depth/node limits precede JSON
parsing; bounded sequence and string visitors refuse oversized decoded fields
before participant admission. These bounds and decoder reservation failures
return `BundleError::Limit`, without interpreting parser diagnostic text.
The JSON parser's temporary unescape storage is
bounded by the outer byte limit. Raw step integers fit `u32`; valid coordinates
must also fit the admitted candidate and complete schedule.

Roles must be a unique ordered roster with exactly the selected entry's
membership. Each role's subsequence must cover its entire body exactly once in
instruction order, ending in exactly one Finish. Only Local, Query, Send,
Receive, Loop, Yield, ReturnIf and Finish are supported. Composition, families and
parameters remain refused by program admission. Flat and nested schedules use
the same recursive coverage validator.

Non-null anchors form contiguous groups numbered `0, 1, ...`. Let `L`, `Q`, `S`,
`R`, `C` denote local call, query, send, receive and conditional entry return.
The exact group grammar is:

- `[L]`, `[Q]` or `[C]`;
- `[L, L]`, `[L, Q]` or `[L, C]`, both at the same role;
- `[S, R]` or `[L, S, R]`, with the optional local call at the sender.

Send and receive must be immediately adjacent, at different roles in the same
instance, with reciprocal peers and identical site, schema and full physical
type. A receive has no calculation prefix. A suffix of null anchors contains one
complete `[L?, Finish]` group per role in roster order. Numbered groups cannot
resume after that suffix. No other instructions may remain.

Anchors are supplied grouping coordinates. A coherent reordering of independent
roles can satisfy these checks. The distinguishing client explicitly demonstrates
that such a supplied reorder can consume a second draw before another role's
failed guard. Bundle admission never grants `checked_source`, a statement proof,
or a source-correspondence certificate.

## Message admission

`zkc.run/0` embeds exactly `zkc.program/0` and uses the compact schedule
contract below. Other bundle or embedded program tags refuse without fallback.
The bundle admits each complete physical message type supported by the installed
native codec, including the variable-size frames defined by
[structured messages](../formats/messages.md). It retains exact width
checks for fixed-width frames, per-message and cumulative byte limits, complete
typed receiver decoding, actual-value handoff and cleanup. A codec declaration
alone grants neither source correspondence nor a statement-validity judgment.
The schedule is independent of runtime message sizes.

## Compact iteration

The `steps` array contains ordinary step objects or
recursive loop objects with exactly three fields:

```text
{"loop": [count-calculation?, loop-header, ... per participating role],
 "body": [step-or-loop, ...],
 "yield": [yield-calculation?, yield, ... per participating role]}
```

Entries and yields are in roster order. Instructions use static preorder indices
within each participant, counting loop headers, nested bodies, yields and the
final return. A header has one anchor shared across its participating roles;
nested actions continue the globally consecutive anchor sequence. Yield entries
have null anchors. Root suffixes retain the ordinary per-role finish grammar.
Stored schedules contain each static instruction once, irrespective of runtime
count. `Bundle::steps()` exposes this static preorder; `segments()` exposes the
recursive schedule. Neither enumerates dynamic occurrences.

Independent admission checks that the recursive schedule covers every flat step
coordinate exactly once in preorder, as well as complete participant instruction
coverage, exact scope parents,
loop nesting, header/yield pairing, and identical loop site/maximum across roles.
Every static loop site must appear in exactly one segment with **all** candidate
headers at that site. Splitting a shared loop into per-role segments is refused.
Only participating roles appear in its body. Ordinary exchange/group rules apply
recursively. Typed visitors bound depth to 64 loop levels and the global step
count across all segments. Positional array substitutes for step/loop objects
are refused; raw outer JSON depth remains separately bounded.

At a reached loop, the driver executes necessary count calculations and validates
each participant's actual count and local bound. A local failure stops with that
participant before agreement testing. Header checks follow roster order and
stop at the first local failure; later roles are not inspected after that stop. If all are valid but disagree, the driver
reports a contract failure without body entry. Zero skips the body and yields its
initial state; otherwise induction runs from zero to count minus one. Child loop
frames borrow immutable captures from their parent. Under the
[retained-value ledgers](capacity.md#retained-values-and-logical-work) a borrowed
capture adds no storage; its shared allocations stay charged once while any
binding retains them, and inline values are charged per frame/iteration. The
destination stores names, not another retained payload. Live service leases
belong to the entry and survive inner frame return.

Reports, transfer hooks and cancellation checks include the complete outer-to-inner
iteration path. Reached headers record `loop_count` and whether `loop_started`;
failed validation/agreement does not claim body entry. Ordinary runner polling at
a loop header or yield stops with `program-control-cut`; only explicit program control
methods may cross those boundaries after host agreement. Misapplied action or
delivery methods return `WrongAction` without polling or advancing such a cut.
`enter_loop` retains a local count-bound failure as a stopped outcome,
just as `loop_count` does. Count disagreement is
reported as `DriverFailed(Contract)` with detail `loop-count-disagreement`. Dynamic dispatches and
reports obey the ordinary driver budget; compact code does not authorize
unbounded runtime work. Stops/cancellation preserve completed messages and draws,
then release all endpoint leases through normal finalization.

## Wire and receive contract

Scalar/group wire types use the exact default representations of the
[structured native message grammar](../formats/messages.md): Boolean,
BLS Fr/G1, BN254 Fr/G1/G2, KoalaBear base/ext8 and Ristretto scalar/group.
They reuse the installed `ZKCV` version-0 frames, including recursively nested
sequences and variants. This bundle follows installed native codec support;
proof deployment adds its own admission and authority checks.
Unsigned `index@native.index/0` is also supported: 14 bytes, with header
`ZKCV`, byte `0`, tag `31` (`0x1f`), then exactly eight little-endian bytes.
The [structured extension](../ir/mathematics.md#native-array-boundary)
also admits complete BLS field-array identities with frame size `6 + 32*N`.
Unlisted physical identities and non-default representations are refused before
runner construction; sharing a logical kind does not establish codec support. The installed structured and
variable-size codecs described above are also admitted. Scalar parsing rejects noncanonical integers and trailing bytes;
group parsing checks canonical compression, curve membership and subgroup
membership. Boolean payloads are exactly zero or one.

Typed decoding checks exact type, length/header/tag, policy limits and canonical
parsing in that order. `NativeWireError::Invalid` carries one closed reason:
Length, Header, Boolean, Scalar or Group. Limit and Backend describe failures
before accepting a receive. No backend error text is parsed to recover this
classification.

`Runner::complete_receive` applies only to programs with an already
pending Receive and an exact matching cut. It never polls to expose the request.
A stale/wrong cut, wrong decoded type or nonserializable decoded value is a
nonadvancing API refusal. Once the attempt is accepted, instruction accounting
runs first, malformed bytes stop with `StopKind::Decode`, and a decoded value is
validated and retained using the existing runtime contracts. Runtime instruction
or retention failure is Limit. Backend validation failure remains Backend,
including resource failures reported through the existing opaque backend trait.
Successful binding advances exactly once. Delivered and Stopped both denote an
accepted completion.

## Joint dispatch and handoff

The host supplies a fresh session ID, exact named role inputs and pre-bound
backends. One backend type is used across the roster. Before construction, invalid
session/membership, data-input arity/type mismatch or failed report reservation
returns `StartError` with all original inputs and backends. Runners are then constructed in roster order from
one admitted candidate. Each constructed runner must have no family ingress.
A runtime loading error becomes `DriverFailed(Setup)`; already entered roles
still pass through finalization. Every supplied backend returns to the host.

Before polling the next scheduled owner, the driver inspects its exposed action
kind and site without advancing it. Inspection distinguishes a loop yield from
a root return; only the explicit control API crosses the yield. A mismatched schedule is a driver contract failure;
it must not poll an unrelated control cut and turn that fault into a participant
stop. A local call or query executes exactly
once, then its stop status is inspected without exposing a successor. Finish
exposes that role's return and performs its ordinary runtime cleanup. A false
returned Boolean is normal completion; the driver has no inferred verifier or
acceptance output. Completion additionally requires every role to have returned
and the pending-message slot to be empty.

There is one session-owned Empty/Payload slot. A send checks its exposed cut,
static type and dynamic payload type, then encodes bytes. The driver checks both
adjacent dispatch budgets, wire counters and already reserved report capacity
before `take_send`. After a successful take, the owned byte vector moves into
the slot without allocation. If `take_send` fails after halting the role, the
participant stop is primary.

At Receive dispatch, after the host cancellation check and before polling the
receiver, a synchronous hook may replace the current bytes. It cannot select a
role or a different exchange. An error, oversized replacement or exhausted wire
budget preserves the committed original bytes. A successful replacement becomes
the pending payload; the report records original and replacement lengths. A
receiver exposure stop or decoder Limit/Backend leaves the slot occupied. An
accepted `complete_receive`, including Decode or runtime Limit, clears it once;
an API refusal preserves it. The report owns any payload still pending at exit.

Default driver caps are 32768 dispatches, 4096 bytes per wire payload or hook
replacement, and 16 MiB accumulated original plus replacement bytes. Hosts may
lower these caps. `ValueBudget` separately controls runner retention; the joint
driver requires its live and cumulative charges to fit 64 MiB and 256 MiB.
`RunLimits.work` separately selects instruction, iteration and logical-work
ceilings, the last at most 4 GiB. Requests above
any installed driver ceiling refuse before entry and preserve caller-owned inputs.
`Report.limits` records the requested policy without silent clamping. The lower-level
`Runner` refuses instruction, iteration and logical-work allowances above its hard
ceilings but permits configurable live and cumulative retained-value budgets. Its 64 MiB
individual-value ceiling remains independent of those aggregate budgets.
The driver reserves reached-step and result-port capacity before any entry.
Cancellation includes the bounded host reason and can occur between send and
receive; the committed message remains in the resulting report. This policy has no asynchronous queue or readiness
scheduler.

## Observation and finalization

`inspect_program` borrows unpolled/pending/returned/stopped state without preparing
work, reading the live environment, cloning a payload or calling the backend.
`poll_ref` has ordinary polling effects but borrows the resulting action, including
its diagnostics. The driver uses it to avoid copying an entire cleanup-error list.

Every ordinary exit after initialization uses one finalization path:

1. Freeze Completed, ParticipantStopped, DriverFailed or HostCancelled.
2. Inspect every role and run its bounded read-only resource observer before
   cancelling any peer. A stopped/returned role has already done local cleanup.
3. Cancel remaining nonterminal runners in roster order.
4. Inspect cleanup results and observe resources again, then recover backends.

Reports retain each accepted receive's Delivered/Stopped result, the reached
dispatch prefix, supplied anchors, exact lowered sites,
wire usage, pending bytes, pre-cancellation states, later cancellation states and
all returned outputs. Each copied backend/observer diagnostic is limited to a
4096-byte UTF-8 prefix with an omitted-byte count. At most 32 cleanup errors per
role snapshot are copied, with an omitted-error count. Runner-owned diagnostics
retain their existing independent behavior. Observer failure is supplementary
and never replaces the primary outcome. Observers must release resource locks
before returning and must not call runners or mutate resources. They own the
meaning of their resource summary; an unknown residual state must remain unknown.

These guarantees cover ordinary returned outcomes. Host callback panic, allocator
abort and process termination have no finalization guarantee. Timing is the
lowered demanding call's timing: total source math is not claimed to fail eagerly
at its original textual position.

## Assurance and scope

Generated Schnorr, service-order and partial-inverse clients exercise this
profile with real backends and independently stated expectations. They provide
bounded implementation evidence. Native Lean semantics, independent source
correspondence, cryptographic soundness, general composition and network
transport remain separate work. The structured profile adds bounded polynomial
realization and a selected reduction/terminal check with its own report scope.


## Installed host and authority

`RunHost::admit(bytes, expected_sha256, limits, authority)` checks bounded exact
bytes against an independently supplied SHA-256 digest before structural
admission. `Bundle::admit_pinned` exposes the same identity boundary to custom
hosts. `Bundle::admit` remains structural admission only. Hashing an incoming
artifact and passing that hash back is not authentication. The application must
obtain its expected identity from its trusted compiler or artifact distribution.
A matching digest does not supply native Lean correspondence or a security proof.

`RunHost::layout()` exposes role names and positional data/service interfaces.
`prepare(inputs)` validates all roles, decodes ordinary values and captures and
authenticates key files before issuing execution entropy or entering any runner.
The returned `PreparedRun` borrows its host and is consumed by `execute()`. Every
invocation creates fresh backends and roots. Session freshness is the caller's
responsibility. The host delegates execution to the same general joint driver;
there is no protocol-specific dispatch.

`prepare_typed(&RunInputs)` uses the same preparation and execution path. Its
request contains the session, exact ordered `RoleInputs` (role name, data inputs,
service budgets), and named verifier-key bytes. `InputValue` accepts bounded native
wire bytes, supported immutable native values, RNG/nonce budget declarations,
the verifier key assigned by admitted setup authority, or authenticated
prover-key files or reusable `ProverMaterial`. The latter uses the shared
[authenticated material contract](proofs.md#typed-invocation-inputs) and
`InputValue::ProverKey`; every call retains setup checks and per-operand charges.
The typed `VerifierKey` declaration carries no repeated selector;
the positional adapter checks its named selector against that assignment. `From<Value>`
constructs the immutable-value case. Native values must match the complete
physical type, be duplicable, and belong to the installed native wire profile;
private capabilities and key handles cannot enter through that case. No encoding
roundtrip is required for an in-process value. Native elements must satisfy their
upstream cryptographic library invariants; unchecked scalar constructors cannot
be used to import invalid field representations. Untrusted bytes use `Wire`,
whose decoder checks canonical encoding and element validity.

`InputValue::Variant` names an active alternative by index and supplies its
ordered immutable payload requests. The admitted native type supplies the full
nominal descriptor; the caller cannot replace it. Shape, type, aggregate element
and group counts, retention and construction peak are checked before decoding
payloads. Nested native/wire inputs share this planning path; resources and setup
key handles are not ordinary variant payload constructors. Every wire scan and
native payload measurement consumes cumulative loading work. Whole-value limits
cannot be multiplied by splitting data across payload children.

Both adapters check selected setup associations recursively, backend value
validity, entry constraints and invocation-wide retained/work limits before
issuance. Native data incurs its loading charge even when immutable backing is
shared; wire data also incurs scan/decode work. Inside each runner, entry
retention charges shared storage once. Wire-byte limits apply to encoded
data, while value/collection limits apply to both forms. A native value need not
fit an unused wire buffer. All authorized setup material, including receive-only
keys, incurs scan work before import and a retained charge. Prepared calls own
the loaded data and remain valid after the input request is dropped or changed.

The installed command is:

```text
zkc run-bundle BUNDLE EXPECTED_SHA256 INPUTS
    [--setups=AUTHORITY] [--capacity=CAPACITY] [--limits=LIMITS]
```

Input JSON is an array:

```text
["zkc.bundle-inputs/0", session,
  [[role,
    [[position, exact_physical_type, [kind, value]], ...],
    [[service_position, exact_contract, budget], ...]], ...],
  [[setup_name, canonical_verifier_key_hex], ...]]
```

Positions and budgets are canonical decimal strings. Roles follow the exact
bundle roster; each role's inputs and services are complete and in port order.
Input kinds are `wire` with native codec hex, `rng` or `nonce` with a budget,
`verifier_key` with an authorized setup name, and `prover_key_file` with
`[path, material_fingerprint_hex]`. Services are installed random providers with
budgets at most one million. A resource row's `index` names the original input
position for a capability or service position for a service, as shown in `layout`.
Names/session are 1–128 ASCII alphanumeric or
`_.-` characters. The entire input document is bounded to 16 MiB; key loading
and retained values share an invocation-wide admission ledger across roles.
Each planned resource reserves the backend's conservative capability byte charge.
The installed host refuses transcript-typed entry inputs; it does not invent
an authenticated transcript root from caller bytes. Custom interpreter clients
and constructed proof deployments retain their existing transcript contracts.

Setup authority is application input, separate from invocation key material:

```text
["zkc.bundle-setups/0",
 [[setup_name, expected_key_id_hex], ...],
 [[role, input_position, setup_name], ...]]
```

At most 64 named keys are admitted. Assignments cover exactly every setup-bearing
entry input, including nested public collections, prover keys and verifier keys.
Each material entry must match its authorized identity and canonical encoding.
Invocation key-file paths, budgets and session names require host authorization;
this API is not a filesystem sandbox. A prover material fingerprint selects bytes;
the authorized verifier key supplies setup authority.
All configured CLI inputs, including bundle, invocation, authority, capacity and
limit files, use bounded regular-file descriptors. Raw byte APIs retain explicit
transport-independent ingress.
Received PCS values select among the authorized registry keys using their native
headers. The Host does not promise an independently pinned key at each receive
site; applications must assess this registry-based authority contract.

The capacity file uses `zkc.native-capacity/0`, shared with the native proof host.
The dispatch/wire file is
`["zkc.bundle-limits/0", dispatches, message_bytes, total_wire_bytes, external_work_per_role]`.
Defaults/hard ceilings are 32768 dispatched occurrences, 4096 bytes per message
and 16 MiB cumulative native wire bytes, with 16777216 external-kernel work units
per role. Both API and CLI refuse requests above these ceilings without clamping.
Structural bundle and native-capacity requests likewise refuse above their own
installed bounds. Reports retain the requested admission, capacity and execution
limits. Per-runner instruction, iteration, logical-work and retained-value
budgets are separate from structural schedule size and runtime dispatch
occurrences.

`zkc.bundle-result/0` retains the primary outcome, reached schedule, pending-wire
metadata, role states before/after cancellation, outputs, usage and backend work.
After issuance begins, ordinary failures return a report and retire every issued
capability and managed service, including partial initialization. Retirement or
output encoding errors are separate diagnostics; they do not erase the primary
outcome. Reports identify active frames and internal resource units after cleanup.
Returned resource units remain in the owning backend and outputs; the report
validates and deduplicates their identities before comparing the live-unit count
with `retained_output_units`, including a role that completed before another role
stopped. Invalid result custody adds a `returned-unit` diagnostic and may also
violate the residual count; both diagnostics preserve the primary outcome. This custody is distinct from issued-root retirement.
Preparation refusals have no issued execution resources. Cleanup does not roll
back consumed entropy, transitions or previously reached effects, and is not a
promise about process crashes or allocator failure.

CLI preparation refusals have `status: refused` and phase `arguments`, `admission`
or `inputs`. Partial issuance and runner construction use `status: setup-failed`
and phase `issuance` or `construction`; an available execution report retains its
original driver outcome and usage. Execution uses `status: executed` and phase
`execution`. Reporting/cleanup errors change status to `diagnostic-failed` without
replacing the phase or primary outcome. Capability and service rows both put public
counters under `state`; service rows also record lease/poisoning state.

The CLI succeeds only on completed execution without reporting/cleanup errors.
A returned `false` is an ordinary output; application acceptance must select and
interpret the intended result. See the [bundle walkthrough](../../runtime/bundles.md)
and [named Entry execution](../../runtime/entries.md).
