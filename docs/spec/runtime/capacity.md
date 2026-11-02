# Runtime capacity

This native contract defines operational ceilings. Sufficient but different
ceilings preserve successful proof bytes; they do not guarantee completion.

## Application capacity

`NativeDeployment::with_capacity` and CLI `--capacity=PATH` select operational
ceilings independently of the authenticated deployment, inputs and proof.
Successful proof bytes are unchanged when different ceilings are sufficient.
The CLI reports the effective record, including defaults:

```text
["zkc.native-capacity/0", "elements", "groups", "wire_bytes", "value_bytes",
 ["instructions", "iterations", "logical_bytes"], ["live_bytes", "total_bytes"]]
```

All entries are canonical decimal strings. The file is at most 4 KiB and has
exact arity; unknown fields or tags refuse. Each field names one Host policy
allowance. A selection above the maximum refuses with `native-capacity-limit`;
it is never clamped. Where the default equals the maximum, a Host can only
lower the allowance.

| Field | Unit | Default | Maximum | Scope |
|---|---|---|---|---|
| `elements` | Numeric elements in one collection or complete nested message | 65,536 | 1,048,576 | Operation |
| `groups` | Group points in one collection or complete nested message | 4,096 | 32,768 | Operation |
| `wire_bytes` | Bytes of one canonical wire frame | 16 MiB | 16 MiB | Operation |
| `value_bytes` | Retained bytes of one native value | 64 MiB | 64 MiB | Operation |
| `instructions` | Executed instructions | 1,000,000 | 2^32 | Runner; Invocation in a Function |
| `iterations` | Entered loop iterations | 100,000 | 2^32 | Runner; Invocation in a Function |
| `logical_bytes` | Logical work bytes | 4 GiB | 4 GiB (2^32) | Invocation |
| `live_bytes` | Live retained payload bytes | 64 MiB | 64 MiB | Invocation |
| `total_bytes` | Cumulative fresh allocation bytes | 256 MiB | 256 MiB | Invocation |

Scopes are the extents over which a counter accumulates: one operation (a
value, collection, frame, message, service, admission algorithm or call), one
participant runner (cumulative across the attempts of one proof call), one
attempt, one invocation, whose
[accounting root](#invocation-ledgers) runs from input preparation through
output publication, or one admitted Entry across all of its calls. In every invocation each field selects one allowance. The
last three are the invocation's: they are the allowances of its
[accounting root](#invocation-ledgers), which charges every Host allocation of
the invocation, from request conversion, context and loading through
diagnostics and result products, and every byte of every participant runner in
Run, Proof and Function invocations alike. A runner's logical work, fresh
allocation, live retention and withheld output capacity are charged there as
they occur, and storage it releases is released there. No runner keeps a byte
allowance of its own beside the root. There is no separate root allowance: the
maximum of each field is the most a record selects, and usage reported on a
refusal never exceeds the selection.

Instructions and iterations are the fuel of each runner. The root of a Run or
Proof invocation pools no fuel: it meters no instruction or iteration. In a
Function invocation the interpreter and every reached child share the root, so
the two fields instead select the meter they pool there, at invocation scope,
and that meter is the only fuel limit of every reached child's runners, which
keep no fuel of their own
([Function instructions and iterations](#host-allowances)). A Function differs
because its aggregate work must be bounded across its children; a standalone
roster never pools its runners' fuel.

The instruction and iteration counters are 64-bit and charged one unit at a
time after their bound check, so no selected budget can overflow them; loop
indices and origin iterations are 64-bit too. The maximum of 2^32 matches the
logical-work maximum and keeps every reported counter an exact integer for JSON
readers, including JavaScript Hosts. Records, ledgers and reports carry these
three counters and their selections as 64-bit integers, never as pointer-sized
integers, so the 2^32 maxima keep their exact value on 32-bit targets such as
wasm32, where 2^32 does not fit a pointer-sized integer. The one million
instruction and 100,000 iteration figures are defaults, not limits of
meaning: a Host authorizes more work explicitly in this record. Numeric
elements and group points are counted across a complete nested message, not
separately for each child collection. For
the QAP matrix sequence, the nonzeros across A, B and C share the element ceiling:
three matrices with 25,000 entries each exceed the default 65,536 aggregate
limit even though each matrix fits individually. A zero group collection ceiling does not
forbid an independently decoded fixed scalar group value. Count ceilings do not
promise that many values fit: wire size, retained backing, decode scratch and
live/cumulative budgets all apply. For example, a 32-byte scalar vector reaches
the 64 MiB decoding peak bound before 1,048,576 elements. The 16 MiB invocation
JSON envelope also counts hexadecimal text and duplicated public/data rows.

Entry function output conversion preserves owner validation for standalone
native leaves, including leaves in source products. Constructing a native
variant checks its complete active arm's element/group totals and retained
construction peak. Opaque opening-state collections count handles, not elements
of their backing tables; singular key/state handles add no backing-element
collection count. Retained-byte and owner validation limits still apply.
Before each native payload measurement, the Host charges its conservative
retained-byte bound to the invocation-wide logical work allowance, including
repeated uses of shared data. Immutable sequences and variants retain this
bound, so computing their charge does not traverse their payloads. Standalone
output leaves need no such scan.

The selected policy reaches native data loading, backend kernels, setup import,
service registry and runner budgets. Attempts cannot exceed these invocation
ceilings. Signature-only deployment admission uses a dummy default backend;
it loads no invocation payload and grants no capacity. Existing setup/provider
limits and the separately configured external-work ledger retain their owners.
Input loading charges the invocation root: its loading work, file reads and
decoding included, as logical work, unit for unit, and the loaded pool, captured
references and imported setup material as fresh and live bytes. Each loading
also keeps operation-scoped sublimits beside the root: its pool and its entry
occurrences within the record's live and fresh byte selections, a value count,
and its own [loading work allowance](#host-allowances), in loading work units
rather than bytes. A refusal names the loading allowance that was exhausted, whether the
sublimit or the root refused: `artifact-input-work-limit` for loading work and
`artifact-input-bytes-limit` for loaded input bytes, as for every
[root refusal](#root-refusals). Canonical public values needed by
the selected role are admitted once and reused after checking exact data-row
bytes and physical layout. Other public values are checked and discarded. The
root does not bound total process memory. Byte
preflight for native wire inputs precedes decoding; loading admits the decoded
value afterward, so a reduced loading ceiling alone does not prevent a single
decode allocation permitted by the backend value ceiling.

The [joint Host](../../runtime/bundles.md) uses the same capacity record. The group
quota covers one collection or complete nested message. It is not
a cumulative per-proof subgroup-work bound: many standalone G2/GT messages remain
bounded by proof size and execution limits. Neither this count nor the instruction
budget measures CPU time.

## Retained values and logical work

Each runner keeps three ledgers, and charges each of them to its invocation's
root as it goes. Each value has a conservative retained
charge, which the per-value ceiling bounds. The installed value adapter
partitions that charge into storage owned by one binding, such as an inline
scalar, and the immutable allocations it shares. A shared allocation's charge
includes the inline storage it holds, such as a collection's element slots.

The CPU adapter reserves 80 bytes per inline value or collection value slot,
with a compile-time bound on the complete native value enum. BN254 target-group
values use shared immutable backing: their charge includes the 384-byte target
and a 256-byte wrapper allowance. BLS12-381 G1 and G2, BN254 G2, Edwards, Ristretto
and resident blst G1 points use immutable backing with a complete 512-byte
profile. Wide three-coefficient rounds (BLS12-381 Fr, BN254 Fr, Ristretto
scalar and KoalaBear octic extension) use shared immutable backing with a
256-byte profile; smaller rounds remain inline. A variant is a shared complete
node with an owned exact-length active payload; its 256-byte header allowance bounds the node and Arc counters.
Aliases retain each actual allocation once; equal
independent targets retain distinct allocations. Capability handles retain their
512-byte profile, and larger shared group payloads retain their own profiles.
These storage charges do not change canonical wire bytes or execution quotas.

Aggregate payloads report immutable logical descriptors and physical child
layouts as separate backing allocations. Their charges include all alternatives,
including inactive variant arms and nominal resource domains. Two values sharing
these actual allocations retain them once; separately parsed equal descriptors
remain distinct. Expanded per-value, admission and codec bounds still count
metadata at every occurrence. A descriptor allocation grants no payload-validation
evidence: validation reuse identifies the immutable payload itself, and capability
checks remain live. Field arrays and fixed vectors partition their descriptor and
element storage in the same way. Their shared immutable physical-layout
wrappers remain covered by the unchanged 1,024-byte view allowance, with a
compile-time size check. No allocation is free merely because it is metadata.

- **Live bytes** count each shared allocation once while any live binding, view
  or container retains it, plus the owned storage of every live binding. A view
  or collection that retains a parent allocation keeps the parent's whole charge
  live until its last reference ends.
- **Total bytes** count each shared allocation once, when a kernel, service,
  entry input, received payload, literal or variant construction produces it,
  plus owned storage at every binding. Captures, arguments, carried values and
  results that cross frames allocate nothing. Release never refunds this ledger.
- **Logical bytes** count work at every kernel and service invocation: the
  operand bytes read and the result bytes newly allocated. Operands are charged
  at their full retained charge at every use, however their storage is shared.
  An installed kernel may declare a smaller read extent; it bounds every operand
  byte the kernel body reads and never exceeds the full charge. Native operand
  admission can additionally walk nested values; its sequence-work ledger
  bounds those walks separately. The native
  row opening declares its row and authentication path; element and handle
  accessors and length queries declare one handle and index.

Allocation identity is the address of a live immutable allocation, recorded
only while a runner binding holds it, so a freed address that is reused counts
as a new allocation. Equal contents never establish identity: separately
created equal allocations are charged separately. Identities never appear in
reports, proofs or semantic observations. An adapter that reports no sharing
is charged in full at every binding. A kernel's output allowance is the
minimum of the per-value ceiling and the remaining live, total and logical
budgets; it bounds storage the kernel newly allocates, not storage its result
shares with its operands.

A capability-free immutable value bound under the same physical type reuses its
successful backend validation for aliases. A borrowed runtime-owned `Retained`
view also lets the backend reuse validation of intrinsically typed immutable
sequence subtrees. Only allocations still held by this Runner are present;
entries disappear with their final reference. Numeric storage whose validity
depends on its physical type does not use subtree reuse. Capabilities are always
checked against current custody. Backend
policy, setup authorization, frame custody and capability checks remain required.
External calls and codecs receive no retained-validation evidence.

Local and participant return/yield handoffs keep shared backing in the ledger between region
exit and caller binding. These internal references add no value binding or
inline charge. They are released after transfer and on every failed transfer,
loop step or frame leave. This preserves storage accounting while avoiding a
repeated walk of a carried immutable subtree.

For example, a prover that commits 65,536 extension-field rows once and opens
64 rows from a repeated phase capturing the opening state retains the vector
and the 6.29 MB state once; each opening allocates and reads only its row and
path. This completes under the default record.

## Shared invocation execution policy

`ExecutionLedger` is the handle of an [invocation root](#invocation-ledgers).
Its cloneable handle shares atomic logical-byte, cumulative fresh-byte and
live-byte allowances across the Host scopes of one invocation and every
participant runner. The Host builds a Run or Proof root from the selected
capacity record's byte fields with `ExecutionLedger::bytes_only(ValueBudget,
logical_bytes)`; it pools no fuel, and a fuel charge to it refuses. A
Function's root, `ExecutionLedger::new(ValueBudget, WorkBudget)`, also pools
the instruction and iteration meter of its interpreter and children. Every
participant of a run, every proof runner and attempt, and every Function child,
joint participant or numerical child, receives a clone of the same handle from
the Host. Each runner keeps its own usage counters and backend-local
retention/validation ledger, but no byte allowance of its own, an attempt's
runner included. A runner of a root that pools no fuel keeps its own
instruction and iteration fuel. A runner of a root that pools fuel, as a
Function's children are, charges the root's meter and keeps no fuel of its
own: its own budget is the interpreter's hard ceiling, which no pooled
selection exceeds, and before each instruction it checks the root's meter, so
the meter is its only fuel limit. Creating a child never replenishes shared
capacity. Native sequence, external and Ring work are
[Host allowances](#host-allowances); wire/proof transport, loading and scratch
also charge the root while keeping their own allowances. Hosts apply
cumulative policy to those counters separately.

Each runner holds its live retention in the root as it occurs. Retaining a
value charges its logical work, fresh bytes and live bytes to the root
together, all or nothing, settling any output capacity withheld for it; a
refused retention commits none of them. Releasing storage returns its live
bytes to the root once the values that held it are destroyed, including
payloads an action still owns after their scope closed. Simultaneously live
parent and child runners therefore count together, even while the parent is
suspended. This is conservative: separate runners, and a runner and its Host,
count shared aliases independently. Within one instance, the existing backing
identities still avoid duplicate shared-storage charges. This policy is neither
actual allocator accounting nor peak RSS. `reserve_live(bytes)` gives
Host-owned storage the same explicit live guard; `charge(work, fresh_bytes)`
debits known Host work/storage before its effect.

Instruction and iteration charges precede their steps. Operand logical work
precedes backend application. An allocating kernel withholds shared fresh and
logical output capacity before application and receives the clipped output
allowance, which the root's remaining live allowance also clips. Capacity
withheld by an in-flight call is unavailable to concurrent calls and reported
separately by `snapshot()`. Successful calls settle their
provisional allowance to actual admitted output charges. Unused provisional
capacity was never committed work. A failing call conservatively commits its
entire withheld allowance because partial allocation cannot be observed. Service
queries reserve their complete installed reply bound before their effect.
Committed instructions, iterations, logical work and fresh allocation are never
refunded on release or unwind.

For shared execution, trusted Value adapters advertise constructor allocation
bounds before scalar/variant construction. The generic scalar default is 512
bytes; the CPU adapter supplies its 80-byte inline bound. The
variant default covers its descriptor, conservative payload slots and full
payload charges. Larger adapters must override these bounds. Insufficient
capacity refuses before the constructor runs, even if the actual value might
have been smaller. Induction temporaries have an additional conservative fresh
charge before their later frame binding. Local frame inputs reserve their known
transfer charge before backend entry. The per-value, structural, scratch and
backend-specific preallocation contracts still apply independently.

Cleanup refunds only live allowance, once all stopped scopes and outstanding
handoffs have released their storage. Successful terminal values keep their
live bytes in the runner's hold. `into_retained_outputs()` transfers backend
custody and an optional `RetainedOutputs` guard containing the successful values
and that live hold; an unfinished runner is cancelled. A Host retaining values across a
child call must keep the guard, or separately reserve their storage. Dropping
the guard releases live allowance after dropping its values and never refunds
cumulative work. Borrowing or cloning a value grants no new live allowance.

Shared accounting carries no `Retained` backend-validation evidence. Another
backend must independently validate every incoming value, setup and capability;
allocation identity cannot transfer authority.

## Invocation ledgers

Every Entry kind keeps one invocation accounting root: an `ExecutionLedger`
whose live, fresh and logical-work allowances are the selected capacity
record's `live_bytes`, `total_bytes` and `logical_bytes`. It runs from input
preparation through output publication. Before each effect, it charges the
Host-side work and storage of:

- request document decoding and request conversion;
- setup imports, including reuse of a persistent import, and input loading
  with its file reads;
- common-input inspection, context production and canonical encoding;
- the binding root, proof buffers of every attempt, received proof payloads,
  and joint wire transport and payload decoding;
- diagnostics: joint report rows and their shared dynamic paths, Function
  call receipts, and every rendering of a joint or proof report's diagnostics;
- returned values the Host retains, result reconstruction and every result
  encoding.

It charges every participant runner's bytes too, as the runner executes:
logical work, fresh allocation, live retention and withheld output capacity.

| Entry kind | Root | Runners |
|---|---|---|
| Run | Created at preparation from `HostLimits::capacity`; a run started by an outer invocation uses the outer root | Each participant charges its bytes to the root and keeps the record's instructions and iterations as its own fuel |
| Proof | Created from `ProofOptions::capacity` (`NativeDeployment::with_capacity`) at the call's preflight (`preflight_call`, `preflight_document_call`) or at `prove`, `verify` or `prove_attempts`, and kept by `ProofCall`, `ProofReport` and `ProofResult`; a proof started by an outer invocation uses the outer root | The selected role's runner, and each attempt's runner, charge their bytes to the root and keep their own fuel, cumulative across the attempts |
| Function | Created at preparation from `FunctionOptions::limits.capacity`, with the pooled instruction and iteration meter, and shared with every reached child | Child runners charge their bytes and their instructions and iterations to the root; the pooled meter is their only fuel limit |
| Backend run | `BackendRun::execute` creates it from the byte budgets of the selected `RunLimits`; the report keeps it | Each participant charges its bytes to the root and keeps the selected instructions and iterations as its own fuel |
| Backend participant | `InputBoundBackendRun::start_role` creates one for each started participant from the selected byte budgets, an invocation of its own as in an independent process | The started runner charges its bytes there and keeps the selected instructions and iterations as its own fuel |

Every participant runner charges the root as it executes, and a runner of a
Run or Proof invocation keeps its own instruction and iteration fuel, so a
standalone roster never pools fuel while the root bounds the bytes of the Host
and of every runner together: runners that each fit the record alone can
together exceed it. When the root cannot afford a runner's charge, its byte
charge or a Function child's charge of the pooled meter, the runner stops with
its own limit stop, and the report keeps both the runner's usage and the
root's ([reported usage](#reported-usage)). The Host and the runner
exchange custody at the runner's boundaries. Loaded inputs pass to the runner
when it starts: the Host's reservation of them ends there, and the runner
charges them as it retains them. Returned values pass back when it finishes
with the live hold of their bytes in the root, so custody moves without a gap
and without a second charge.

Retained results keep their reservations: `RunReport`, `ProofReport`,
`ProofResult` and `FunctionReport` hold every live allowance of their values,
proof bytes and imports until they are dropped. Each encoding of a retained
result (`RunReport::encode_results`, `ProofResult::encode_results` and
`encode_results_owned`, `FunctionResultEncoder::encode_report`) is a new
buffer: it charges that buffer to the root and keeps its live allowance until
the buffer is dropped. Repeating an encoding charges the new buffer and nothing
else. An owned encoding keeps the result, and so its root and reservations,
alive for deferred readers such as browser getters, and every copy a reader
takes is a new allocation charged to the same root. Publication therefore has
no separate allowance.

Diagnostics are charged where they are retained and where they are rendered.
Joint report rows and their shared paths, and Function call receipts, hold
their live bytes in the root while the report or journal exists. Rendering a
joint run's diagnostics (`HostReport::diagnostics`) repeats each row's control
path, so the Host first charges a bound proportional to the rows, their path
strings and iteration numbers, the roles and the retained records; when the
root cannot afford it, the rendering is the bounded summary with
`"diagnostics": "omitted"`. `HostReport::encode_outputs` charges each encoding's
bound and holds its live bytes with the encoding; one the root cannot afford is
unavailable with `bundle-output-limit`. Rendering a proof report's diagnostics
(`NativeProofReport::diagnostics`) copies every attempt, resource and cleanup
record, with the complete origin paths of stops and early returns, so the Host
first charges a bound of those records and strings to the call's root, which
for a Function's proof child is the Function's root; when the root cannot
afford it, the rendering is the bounded summary with
`"diagnostics": "omitted"`. Each rendering charges again. Diagnostics that a Host never renders charge nothing
beyond their retained storage.

### Reported usage

Every report of an invocation renders its root's usage in one shape, under the
key `invocation`: the run report (`HostReport`, the CLI `zkc.bundle-result/0`),
the proof report (`NativeProofReport`, under `execution` in the `zkc prove` and
`zkc verify` reports and at the top level of the `zkc bundle prove` and
`zkc bundle verify` reports), the Function report (`FunctionReport`, under
`execution` in the `zkc run` report), the bounded summaries a Function's call
receipts keep of its run and proof children, and each numerical child's
receipt:

```text
{"instructions": N | null, "iterations": N | null, "logical_bytes": N,
 "total_value_bytes": N, "live_value_bytes": N}
```

`logical_bytes`, `total_value_bytes` and `live_value_bytes` are the root's
committed logical work, its cumulative fresh bytes and the live bytes it holds,
which the record's `logical_bytes`, `total_bytes` and `live_bytes` bound; they
take the names of a runner's own usage, which reports render beside the root's.
`instructions` and `iterations` are the pooled meter's, in a Function's root,
and `null` in a root that pools no fuel. The figure is the root's usage when
the invocation's execution ended: after every runner, cleanup and, for an
Entry, its result reconstruction. A receipt's figure is the root's usage when
that child ended. Renderings of diagnostics, result encodings and copies charge
the root beyond it, each again, so every rendering of a report reports the same
figure. A refused or stopped invocation reports the usage its committed charges
reached, beside each runner's own, so the bound that was met is observable. A
record that selects exactly the reported logical work or fresh bytes leaves no
room for the renderings and encodings that follow.

### Root refusals

Each charge that the Host or the runtime makes in the root reports the code of
its charged item, never the ledger's generic limit and never the code of a
limit the item's own format or allowance sets. Every charge to the root is all
or nothing: its logical work, its fresh bytes and the live bytes it holds are
committed together, or the charge refuses and leaves the root's usage
unchanged, so a refused item leaves no residual charge for a later charge to
meet. This holds for every row below, whether the item has separate work and
bytes codes or one code for both. A refusal of an item with separate codes
reports the bytes code when the root's fresh or live byte allowance refuses,
including when its logical work allowance refuses too, and the work code when
only the logical work allowance does. Committed charges are never refunded.

| Charged item | Work refused | Bytes refused |
|---|---|---|
| Input loading, its file reads, captured references and imported setup material | `artifact-input-work-limit` | `artifact-input-bytes-limit` |
| A proof's binding root, the canonical encodings of its public values and the public copies of its verifier keys | `native-proof-binding-work-limit` | `native-proof-binding-bytes-limit` |
| A received proof retained for its record codec | `native-proof-received-work-limit` | `native-proof-received-bytes-limit` |
| A completed attempt's proof retained by the call | `native-attempt-proof-work-limit` | `native-attempt-proof-bytes-limit` |
| A Function's invocation context, frames, environments, call receipts and typed values, and its children's requests and results | `entry-host-work-limit` | `entry-host-bytes-limit` |
| Request documents and their conversion | `entry-request-limit` | `entry-request-limit` |
| Common-input inspection and context encoding | `input-binding-work-limit` | `input-binding-bytes-limit` |
| Result reconstruction, named result encodings and copies of retained results | `entry-output-limit` | `entry-output-limit` |
| A native run's output encodings | `bundle-output-limit` | `bundle-output-limit` |
| A proof's transport: each message buffer and encoding a producer writes, and the work and decoded storage of each message a validator receives | `proof-transport-work-limit` | `proof-transport-bytes-limit` |
| Joint wire transport: each encoded or replacement message buffer, and the work and decoded storage of each received payload | `joint-transport-work-limit` | `joint-transport-bytes-limit` |
| Joint report storage: each reached record, with its region's shared path | `joint-record-work-limit` | `joint-record-bytes-limit` |

The [input-binding format](../formats/input-bindings.md)'s own ceilings refuse
with `input-binding-Limit`, the [proof format](../formats/proof.md)'s own size
limit with `proof-limit`, and the [joint Host](joint.md#joint-dispatch-and-handoff)'s
dispatch and wire allowances with `joint-limit` and its report storage
allowance with `joint-report-limit`, apart from these root refusals. Reading a
received message or payload is its first charge, of logical work alone, and
refuses with the work code; its decoded storage is a second charge.
A Function interpreter's own charge of its pooled meter refuses with
`entry-host-instruction-limit` or `entry-host-iteration-limit`, naming the
exhausted meter. A rendering of diagnostics that the root cannot afford is the
bounded summary rather than a refusal. A child invocation's refusal keeps its
code when it reaches the Function.

A runner's own charge that the root cannot afford stops the runner with its
own limit stop rather than a refusal code.

Reusing a persistent setup import avoids decoding it again, but each invocation
still charges its own retained snapshot, 16 bytes per canonical byte plus 4,096,
to its root. Reuse never resets a cumulative charge or grants authority. Within
one invocation, a second import of identical bytes under the same pin shares the
first import and its charge.

Request conversion charges the named values' description bytes as logical work
and the converted operand list as fresh allocation, before native preparation;
a refusal is `entry-request-limit` at `Preparation`. Decoded request documents
are charged as fresh allocation and held live until conversion. Result
reconstruction charges every returned native value's retained bytes as logical
work and 128 fresh bytes per schema node of the named result before it
allocates, and the report holds the nodes' live bytes; a refusal is the
report's `entry-output-limit`.

Common-input inspection charges each inspected value's retained bytes as logical
work before validating it. A value observation charges its canonical encoding
bound as fresh allocation and holds that live allowance until the comparison
ends. All roles checked for one invocation draw on the same allowance; no
allowance restarts per role. Function preparation validates every deployment's
context, including deployments the call never reaches; that validation decodes
and imports real material, so it charges the root, and a reached child's later
loading is a second real allocation charged again.

## Byte construction

Native `bytes.repeat` and `bytes.join` check byte limits and reserve `256 + 2*n`
output bytes for a result of length `n`, including temporary and immutable
storage. Operand-read and result-retention charges also apply. `join` uses the
sequence validation work ledger: a retained input needs only its root check,
while the full operand-read charge accounts for reading its fragments.

## Host allowances

The Host policy record owns each native allowance beside the capacity record's
fields. Each names its unit and scope and has one default and one maximum,
defined once (`run::Allowances`, with `run::Scope`); a selection above the
maximum refuses without clamping:

| Allowance | Unit | Default | Maximum | Scope | Selected by |
|---|---|---|---|---|---|
| Ring work | Ring expression substitution work units | 2^28 | 2^28 | Runner (per role) | `HostLimits::ring_work`, `ProofOptions::ring_work` |
| Sequence work | Three units per examined nested node and call | 16,777,216 | 16,777,216 | Runner (per role) | `HostLimits::sequence_work`, `ProofOptions::sequence_work` |
| External work | One unit per hash call, hashed byte, permutation, observe or sample | 16,777,216 | 16,777,216 | Runner (per role) | `HostLimits::external_work`, `ProofOptions::external_work` |
| Service draws | Draws | 1,000,000 | 1,000,000 | Operation (one managed service or transcript) | Request service budgets and `transcript_budget` |
| Interface work | Work units of one interface admission algorithm: schema validation, or supply reconstruction with public selection indexing | 1,000,000 | 1,000,000 | Operation | `HostLimits::interface`, `ProofOptions::interface` (`InterfaceLimits::work`) |
| Interface descriptors | Retained descriptor bytes of the schema summaries, of each reconstructed supply plan and of a Function's native descriptor cache | 16 MiB | 16 MiB | Operation | `HostLimits::interface`, `ProofOptions::interface` (`InterfaceLimits::descriptor_bytes`) |
| Dispatches | Joint and Function dispatch occurrences, including repeated loop steps | 32,768 | 32,768 | Invocation | `HostLimits::steps` |
| Function service draws | Draws reserved for children before their roots are issued | 64,000,000 | 32,768,000,000 | Invocation | `FunctionOptions::service_draws` |
| Journal events | Retained Function call receipts, including failed calls | 256 | 4,096 | Invocation | `FunctionOptions::journal_events` |
| Attempts | Completed or discarded trials of one producing proof call | 1 | 1,024 | Invocation | `AttemptOptions::count`, `FunctionOptions::attempts` |
| Attempt proof bytes | Proof buffer bytes of one attempt, including framing | 16 MiB | 16 MiB | Attempt | `AttemptOptions::proof_bytes` |
| Function instructions | Instructions of the Function interpreter and every reached child | 1,000,000 | 2^32 | Invocation | `FunctionOptions::limits.capacity` (`instructions`) |
| Function iterations | Loop iterations of the Function interpreter and every reached child | 100,000 | 2^32 | Invocation | `FunctionOptions::limits.capacity` (`iterations`) |
| Loading work | Loading work units of one input loading: one per input node, wire scan or native measurement, plus each byte read and each retained estimate, including cache hits | 2^28 | 2^28 | Operation (one input loading) | `HostLimits::loading_work`, `ProofOptions::loading_work` |
| Public bytes | Wire bytes of one proof call's public statement, counted at every role operand a public value initializes, including shared owners | 64 MiB | 64 MiB | Operation (one proof call) | `ProofOptions::material`, `HostLimits::material` (`MaterialLimits::public_bytes`), CLI `--material-limits` |
| Reference bytes | Bytes of the named references one memory request binds | 256 MiB | 256 MiB | Invocation | `ProofOptions::material` (`MaterialLimits::reference_bytes`), CLI `--material-limits` |
| Setup bytes | Setup material of one invocation, counted at every copy the Host holds: each verifier-key copy for a proof's public port, and the material of every deployment of a Function invocation | 64 MiB | 256 MiB | Invocation | `ProofOptions::material`, `HostLimits::material` (`MaterialLimits::setup_bytes`), CLI `--material-limits` |
| Retained imports | Retained bytes of the setup imports an admitted proof Entry keeps for reuse across its calls | 64 MiB | 64 MiB | Entry | `ProofOptions::material`, `HostLimits::material` (`MaterialLimits::retained_imports`), CLI `--material-limits` |
| Prepared data | Retained bytes of one prepared datum: its native value and canonical wire bytes together | 64 MiB | 64 MiB | Operation (one prepared datum) | None: the `PreparedData` constructors take the default |

The Function service-draw maximum is one maximal service allowance for every
dispatch a Function can make. The joint Host's message, cumulative wire and
report storage allowances are listed with
[joint dispatch](joint.md#joint-dispatch-and-handoff).

The material allowances (`MaterialLimits`) bound what an application supplies
beside its named values: a proof call's public statement, a memory request's
named references, an invocation's setup material and the imports a proof Entry
retains. None derives from a runner's capacity, even where the numbers agree.
Exceeding one refuses with `entry-input-limit`, `entry-request-limit` or
`entry-setup-limit` respectively. A setup file is read only up to the
remaining setup allowance, and one that it cannot hold refuses with
`entry-setup-limit`. Setup material defaults to 64 MiB, and a Host may select
up to 256 MiB, as large commitment setups need; the other material allowances'
defaults are their maxima.
Imports that do not fit the retained-import allowance are imported for the call
without being retained. A selection above a maximum refuses with that
allowance's own code: `entry-public-bytes-limit`,
`entry-reference-bytes-limit`, `entry-setup-bytes-limit` or
`entry-retained-imports-limit`. A Function's children take the material
allowances of `FunctionOptions::limits`. A browser session keeps its setup and
named input copies within the setup and reference allowances, because every
call binds all of them.

The CLI's `run`, `prove`, `verify` and `common-inputs` commands select the
material allowances with `--material-limits=PATH`. The selection also bounds
the setup material that `--key` and an invocation document read before
execution. The CLI reports the effective record, including defaults:

```text
["zkc.material-limits/0", "public_bytes", "reference_bytes", "setup_bytes",
 "retained_imports"]
```

The record follows the capacity record's rules: all entries are canonical
decimal strings, the file is at most 4 KiB and has exact arity, and another tag
refuses with `material-limits-format`. A selection above a maximum refuses with
that allowance's code. Without the option the CLI takes the defaults.

The capacity record's live, fresh and logical byte selections bound the root
that a Run, Proof or Function invocation creates, whether the CLI's
`--capacity` record, the browser adapter's `capacity` record or an SDK
selection. `NativeDeployment::with_capacity` selects them for a low-level
proof deployment, beside `with_loading_work_limit` for its loading work, and
`BackendRun::execute` takes them in its `RunLimits`. A child invocation charges
its outer root and takes none of its own.

`PreparedData` retains each prepared datum, its decoded native value and its
canonical wire bytes together, within the prepared-data allowance; exceeding it
refuses with `native-data-bytes-limit`. Preparation belongs to no invocation,
so neither a runner's allowances nor a root bound what a datum retains, while
the capacity record still bounds its decoding and every use charges its
invocation's loading.

The Function instruction and iteration allowances are the meter that a
Function invocation's interpreter and every reached child pool in the root,
selected by the capacity record's `instructions` and `iterations`. A Function
differs from standalone runs because its aggregate work must be bounded across
its children: each child's runner shares the root and charges the meter, its
only fuel limit, keeping no fuel of its own, while a standalone runner keeps
its own fuel and a standalone roster never pools it. A child the meter stops
stops with its own limit stop.

A Function takes the same record in `FunctionOptions::limits`. Each reached
child receives what remains of its dispatch, wire, external, Ring and sequence
allowances after earlier children, divided equally across a joint roster, and
its runners charge the record's byte allowances and the pooled meter in the
shared root; a child never replenishes the parent's allowance.

[Numerical calls](numerical.md#managed-construction) additionally bound managed
scratch, result-construction overlap and numerical work in their migrated native
handlers. These per-call backend policy ceilings are separate from the CLI
capacity record and the VM's retained-value ledgers.

[Joint dispatch](joint.md#joint-dispatch-and-handoff) owns dispatch, message,
cumulative wire and report storage limits. [Proof transport](../formats/proof.md) owns proof
framing limits, and [attempts](attempts.md) own retry counts and cumulative
budgets. Loading, setup and backend scratch retain their own limits. These
units do not establish one global peak-memory or elapsed-time bound.

## Maintained scale controls

The STARK library's maintained 256-row, 100-query clients
(`common/tests/protocol/test_stark_library.py`), quartic Keccak with block
sampling and Poseidon2 with octic Merlin challenges, run under the default
record. Each control records its verifier's `execution.instructions` and
`total_value_bytes` from the verify report, with the retained expectation and the
margin to the default budget. A measured count may differ from its expectation by
at most 0.2% in either direction; a change that moves it further updates the
expectation in the same change, so the margin to the default budget is always a
reviewed number. The benchmark execution-count lane keeps the trend of the
Poseidon2 client as case `stark-h256-w1-b2-q100`, with the same LogFinal,
LogBlowup, query count, suite and table realization.

## Loading and capacity

Public declarations count toward invocation loading even when used only in the
binding root. Matching role operands reuse decoded values after exact agreement;
each operand counts toward loading. Entry retention charges their shared storage
once and inline values per operand. Per-value decode preflight
precedes payload decoding. Cumulative loading admission has its own ledger and
can occur after that decoding; it is not a whole-process memory bound.
Key files use bounded regular-file reads and pinned material. Data, entry and
transcript-root capacities are checked before execution entropy.

Nonce/RNG operands and the selected transcript reserve their capability retention
charges before issuance. Sequential attempts reserve one live transcript slot
while retaining cumulative execution work and allocation accounting. JSON,
logical counts, retained values, wire bytes and primitive work have distinct
ceilings; raising one does not raise the others.
