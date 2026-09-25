# Protocol compilation architecture

This chapter describes the boundaries from authored protocols to executable
participants. Common interaction, construction, role projection and selected
physical execution are implemented; broader admission and realization laws below
also constrain future extensions. [Interactive execution](interactive-execution.md)
and [status](../status.md) identify the maintained subset. The [roadmap](../roadmap.md) owns
delivery order, and the [specification](../spec/README.md) and the formal library
remain the authority for meanings and theorems. The laws these contracts owe
include exact versus prefix comparisons and the premises needed for resources,
shared services and a committed terminal.

Sections 2–6 state selected contracts and design rules. They do not by themselves
assert that every described mechanism is implemented; the
[interactive execution reference](interactive-execution.md) and
[status](../status.md) identify concrete supported paths.

## 1. Representations and their consumers

```text
protocol module: common interaction + actual local algorithms + dependencies
    │ resolve an instance; admit entries, resources and operation contracts
    │ select/perform a construction, retaining its changed experiment
    ▼
participant module: actual algorithms, local state, sends/receives and calls
    ├─ verifier acceptance/output interpretation → relation/gadget target
    │ choose implementations; lower domain operations as useful
    ▼
physical module: kernels, storage, representations and participant control
    │ admit the actual artifact and installed bindings
    ▼
Rust role runner + selected driver/transport + external cryptographic libraries

supplied participant / independent artifact entry ──► participant admission
```

The construction checkpoint is explicit but need not introduce a fourth
universal IR. It can transform a protocol module and its dependency bindings.
Polynomial, group, oracle and relation abstractions form an independent domain
dimension. Each can remain inspectable in several representations. An efficient
upstream kernel can implement an operation directly; a smaller operation does
not have to be invented merely to make every path use the same lowering stack.

Common interaction supports composition, phase ordering, challenge dependencies
and participant derivation. Participant algorithms support local control,
availability, independent verifier reasoning and target selection. Physical
plans support storage, locality, kernel choice and executable cost. These
consumers, rather than the number of dialect namespaces, justify the boundaries.

Use `pir` for the common and participant protocol carriers initially, with
different operation forms and module stage declarations; use `plan` for physical
choices. A phase verifier enforces which forms may occur together. Keep common
source and generated role modules as separate artifacts even when they share a
dialect. Introducing `oir` later is a namespace/ownership decision if separate
registration becomes useful, not a change to participant meaning. Keep dialect
definitions and implementation files separated by responsibility from the start.

## 2. Module, instance and local algorithm

A module contains reusable definitions, declared dependencies, selected
instances and exported entries. A definition is code. An instance resolves its
role map, domain/configuration parameters and dependency bindings. A runtime
invocation receives actual values/resources and its invocation path. Code
specialization identity, evidence identity and resource identity are distinct.

The parent instance supplies named child dependencies; an `invoke` refers to a
declared dependency or concrete resolved instance. The resolver checks the
callee's value/resource signature, role substitution and dependency closure.
The current Lean carrier's literal callee plus binding key is the resolved
target of this step, not an implementation of the complete resolver. Do not
clone an entire protocol just to change a child backend. Specialize only the
parameters needed by that body's interpretation or native code.
Declaration admission may validate a module with explicit external signatures.
Executable admission additionally requires every selected body or installed
contract implementation. An encoded architectural sketch passing the former
does not establish an executable protocol or give meaning to missing algorithms.

Use MLIR symbols for definitions, instances, dependencies and entry references;
use SSA for runtime values and capabilities. Symbol resolution must validate
the actual referenced signatures, not just symbol spelling. A public statement
is available separately at each relevant role. Its agreement and connection to
the advertised subject are entry obligations, not implied by a `public` label.

Each `local` region has an owner and explicit captures, block arguments and
results. Its body contains actual domain algorithms or calls with visible
contracts. Use isolated regions to forbid ambient SSA capture and separately
check role availability. Neither MLIR isolation nor ordinary type equality
proves privacy. Pure helpers can use `func`; effectful protocol calls retain
returned/stopped control, instance context and invocation origin. Do not treat
an effectful verifier with receives as a local pure helper.

Public dimensions parameterize a resolved family. A fixed `Nat` in the current
Lean `repeat` does not require native per-dimension compilation or unrolling:
an admitted input `n` can select that family member at execution. A dynamic loop
representation needs correspondence to that selection, checked integer/shape
bounds and agreement wherever multiple roles use the count. The initial source
profile admits fixed public control, local branches and stops. Global choice
requires a later explicit agreement/delivery/merge rule; it is not inferred from
matching syntax in two endpoints.

## 3. Resources and child authority

The reference's `ps_i` and `vs_i` denote separate local resource tuples. They
may contain a transcript capability, random source, immutable opening state,
one-use ticket or service handle. They are not one mandatory transcript token.
Distinguish ordinary immutable data, control ordering and authority over state.

Resource signatures describe use: borrow immutable state, consume and return a
successor, or call a scheme-specific split operation. A permission to copy an
immutable prepared key does not permit copying commitment randomness. A split
random source needs a joint distribution contract. An affine use check cannot
prove independence of correlated randomness.

Adopt explicit capability operands plus admitted runtime resource views. Static
admission checks ownership, availability and path-sensitive use of consumable
ports. Runtime admission checks actual identities, aliases, generations,
legitimate issuance/import rights, instance/subject binding and legal borrowed
views. Distinct SSA arguments can
alias the same resource; two code instances do not mint fresh tapes. Deliberate
sharing is permitted when the declared resource contract supports it.

A child receives only its admitted view, not unrestricted access to every
resource owned by its role. Local adapters implement transitions of that view;
the enclosing executor installs the resulting view back into its authoritative
store on both return and stop. The required law includes residual state and
unaffected resources. The frame and execution correspondence follow from
`run_related` for arbitrary adaptive child computations at one slot of a
homogeneous store. Source tuples need a slot-set or other view implementation
with its own frame law: arbitrary overlapping views do not follow from a
single-slot theorem, and neither does a production resource checker.

Keep `State : Role → Type` in the execution model. It can interpret resource
views and authoritative stores. Do not impose one universal slot algebra on
all protocols. Implement the admitted source/resource profile and its runtime
correspondence together, including failed writes and stale/replayed handles.
Backend allocation outside an admitted store has a separate failure contract;
reserving table memory does not reserve all memory used inside an external PCS.

## 4. Participant meaning and execution

There are two distinct correctness questions:

1. Does splitting source interactions into scheduled send/receive actions under
   one selected driver preserve the complete joint run? The current
   `Compiler.Participant.run_project` proves this for its maintained grammar,
   including stored callees, fixed loops, outcomes, states and events.
2. Does each generated role module implement that role's source obligations
   against arbitrary admitted incoming messages and local services? A direct
   source-role interpretation and a target-role interpreter must answer this
   independently. This connection is not supplied by the scheduled theorem.

Define open role meaning directly from source structure: keep owned local
computations, map incoming/outgoing messages to that role's operations, project
actual calls and loop accumulators, and retain only available values. A missing
incoming packet suspends the role runner; it is not automatically a terminal
`PIR.Stop`. A bounded driver may report incomplete execution under its selected
cutoff policy. A remote private stop does not silently stop this role.
Distinguish that dynamic case from an unconditional syntactic foreign `stop`
leaf: the source has no continuation or return value there. In the first profile,
its direct role interpretation ends as `incomplete`, retaining local state and
revealing no remote reason. It is neither an input wait nor a successful return.
This schema choice needs its own source and projection tests.

The participant execution interface has admitted entry arguments/resources,
owned local state and a continuation/call stack. Advancing it exposes one of a
local contracted action, outgoing packet, incoming-packet request, return or
local stop. Backend work may be coarse; a local action can run a bulk kernel.
These are execution-interface cases, not a fixed C ABI or wire schema.

The synchronous reference driver selects source order and retains complete
joint failure state. It can schedule the same local continuations without
inserting peer-visible `wait` messages into the participant protocol. Its
administrative schedule and observations belong to the selected driver profile.
Exact source/joint-run equality requires an actual correspondence to that
driver; arbitrary decentralized execution does not satisfy it by definition.
Exact comparison also fixes action granularity, initially the source's exposed
local actions. For `P:a; V:check; P:b`, a failing check leaves only `a` executed.
Fusing `a` and `b` across that position cannot preserve this observation merely
because they share an owner. Keep the cut, or use a separately justified observer
and simulation that permit the fusion. Even open-role comparison needs a mapping
of fused actions to observations; prefix equality of raw action lists is not
automatic. Changing the harness observer is a contract change, not a test repair.

Open-role correspondence compares the source-role interpretation with the
generated role under related local services and the same admitted incoming
strategy. Joint-to-open comparison instead relates aligned local prefixes and
delivered messages. A peer may subsequently compute, consume a resource, return
or block after another role has stopped. Do not equate their complete final
states. Progress/fairness, network cancellation, timeouts and a stronger timing
observer need their own profile and proofs. Controller-private observations
must not silently become public observations or security premises.

Generated and independently supplied participants use the same role admission
and execution API. An artifact validator takes actual candidate bytes, public
inputs, configuration/key and application context, and runs without a live
prover. An accepted validator Boolean alone does not establish its advertised
relation: actual input coverage, decoding and all required component connections
remain visible.

## 5. Construction and composition

A construction consumes a resolved common module and the selected dependency
contracts. A `challenge` may elaborate to local sampling plus delivery, but its
construction role, subject, order and original occurrence must remain visible
to the relevant transform. Opaque bodies need sufficient checked summaries or
the transform declines them. A generic handler name is not such a summary.

Fresh public coins, Fiat–Shamir and other oracle constructions are different
interpretations/transformations with different experiment laws. The default
order is construction before participant extraction. Moving either past calls,
inlining or domain lowering needs the actual commutation/frame premises.
For replay, infer which verifier computations are total pure functions of
prover-available values, across real child outputs and control joins. Validate
that derivation; do not infer availability from matching result names. Logical
message positions can remain in framing even if physical delivery disappears.

Subprotocols remain ordinary protocols with signatures and nested calls.
Composition connects actual typed outputs, commitments, statements, keys and
resource successors. CPU, memory, consistency and opening components are
libraries using these mechanisms. No global claim ledger, universal proof bag
or zkVM-only connector is required. Opaque upstream protocol components remain
possible under their contracts, with correspondingly limited optimization
visibility. A security reduction for a composed protocol is a separate theorem
over those actual connections and the admitted adversary/observer model.

## 6. Domains, kernels and a complete first client

The first complete client is `TwoFactorArgument`: prove the Boolean-cube sum of
the product of two original MLEs, then authenticate both evaluations at the
reached vector point. Retain both original tables and their opening state while
Sumcheck uses folded scratch. Committing the pointwise product or opening an
unrelated univariate polynomial changes the statement.

Select the field, coordinate order, polynomial domain, PCS, setup and challenge
construction together. The bounded first concrete profile uses arkworks 0.6.0,
`BLS12-381::Fr` and `MultilinearPC`, with admitted positive arity. It is a
nonhiding interactive test profile with structured setup, not the eventual
performance target or a zero-knowledge deployment.

Keep the maintained logical convention: coordinate 0 selects the high half of
the flat table. Arkworks restricts the low index bit first. The initial adapter
therefore supplies `backend[j] = logical[bitReverse_n(j)]`, retaining the original
challenge vector order. Commit and open that translated original table; folded
scratch never replaces it. Field, arity, coordinate convention and layout/codec
binding must survive artifact admission. A one-time permutation has allocation
and copying costs to measure. Reversing only the final query is insufficient to
match the ordered Sumcheck messages. The abstract table and polynomial identity
holds under the maintained convention; a client that stores in low-bit order owes
the permutation explicitly rather than inheriting it.

The installed Plonky3 field, polynomial and AIR/oracle kernels execute on a
separate path from Arkworks multilinear PCS. A univariate PCS API does not by
itself implement arbitrary MLE-vector openings: connecting another scheme
requires a pinned matching commit/open/verify adapter, or an explicit reduction
with its own theorem and costs. Avoid mixing field representations through
integers or byte casts. [Operation libraries](protocol-libraries.md) state the
installed domain and implementation boundaries.

Support an explicit base/extension embedding descriptor even though the first
coherent arkworks profile uses one field. Restricting a base-field table at an
extension challenge yields an extension-field table, so output representation,
storage and kernel signatures change. This is an early interface requirement,
not a requirement to implement every field/PCS combination in the first goal.
Instantiating a field-parametric Sumcheck theorem over the extension field is
different from proving the embedding/table-source bridge.

Runtime providers operate on owned typed buffers/views and resolved schemas.
Use whole-table restriction, evaluation, MSM, commitment/opening and verification
boundaries where appropriate. Avoid per-element C++/Rust calls, serializing
whole tables at every step, and hiding the authored algorithm in a whole-prover
call. Borrow original immutable state where a scheme permits; consume state
only where its contract requires it. Canonical codecs and malformed-input limits
belong at actual ingress, not every internal kernel call.

## 7. MLIR mechanisms and implementation homes

| Mechanism | Use | Additional zkc responsibility |
|---|---|---|
| Symbols, symbol users and callable interfaces | Shared definitions and resolved call graph | Instance/resource binding, stopped exits and complete dependency validation |
| Isolated regions, block arguments and ordinary SSA | Explicit local captures, logical values and loop-carried state | Role availability, alias/permission checks and actual domain interpretation |
| Effect and speculation interfaces | Prevent generic motion/erasure of observable actions | Request order, stopping, phase and resource laws; nonlocal control is not fully modeled by generic effects |
| Region/call interfaces and dedicated transforms | Inspect control, inline pure helpers, preserve shared continuations | Effectful protocol inlining and returned/stopped successor correspondence |
| Partial dialect conversion and dynamic legality | Retain mixed domain levels; check stage exits | Admission before destructive conversion, actual-source/candidate binding |
| Bufferization and standard numerical lowering | Selected pure/tensor numerical regions | Aliases, admitted immutable views, field semantics and backend ownership |
| Analysis manager and pass instrumentation | Local caching, invalidation and pass diagnostics | Evidence dependencies differ from reusable code/analysis identity |

None of these mechanisms supplies protocol correctness automatically.
Use `arith` only where its integer/floating semantics match the selected domain;
field computation does not become machine arithmetic by sharing a bit width.

Public C++ interfaces live under `compiler/include/zkc/`, with implementation
under `compiler/lib/`. `Support` and `Contracts` own MLIR-free common services
and installed contract facts. `Frontend`, `Source` and `Protocol` own source and
interaction; `Dialect` and `Interfaces` own IR; `Compiler`, `Analysis`,
`Transforms` and `Target` own compiler mechanisms; `Relation` and `Claims` own
their respective consumers. Conversion implementations live in `lib/Conversion/`.
The [component map](../../compiler/README.md#components) records enforced build
ownership, which need not be one library per directory. Tools and tests sit
alongside these libraries.
Common interaction, participant control and domain definitions live in separate
`Protocol.td`, `Participant.td` and `Kernels.td` files. `IR.td` retains the distinct
finite evidence carrier; it is not the definition of the current common route.
Rust remains in `crates/`: runtime admission/execution/custody, concrete backend
adapters and tools. Introduce backend crates only with real dependency/feature
boundaries; no crate per trait is required. Production names describe concepts,
not research-round identifiers.

The common interactive carrier and the finite table reference have separate
consumers. Their actual-candidate checks retain complete failure state and
storage evidence. The finite table ABI does not constrain the interactive
carrier to two fields, one role or control-only lowering.

## 8. Assurance and the next design boundary

Lean owns source/role/plan meanings, transformation and contract laws, reference
execution and selected protocol properties. C++ owns MLIR analysis, transformation
and serialization. Rust owns admitted execution, continuation state, storage,
providers and upstream calls. There is no analysis RPC loop between languages.

Differential testing is the basic native correspondence evidence: generate
admitted source/inputs/strategies, run the direct Lean reference and actual
MLIR/export/check/load/Rust path, and compare the selected complete observation.
Record malformed input, missing data, aliasing, failure after consumption,
instance changes and hostile deliveries. Independent role tests must run without
an honest prover. Shared codecs/primitives in a harness are named assumptions,
not independent evidence for their own correctness. Fuzzing is not universal FV.

Open-role meaning, source formation/resource admission and native extraction
are evaluated at their supported profiles, with actual consumers and failure
controls. Broader concurrency and external-library verification have separate
obligations; their absence does not invalidate those scoped implementations. The committed-terminal security composition must bind the same
original factors, commitments, keys, point and acceptance; assumptions about
the external PCS and setup remain explicit. ArkLib/VCVio may supply matching
theorems through a real semantic correspondence, not merely an import.

The fixed-table committed experiment is the selected one: original factors are fixed
before future challenges and the experiment supplies their honestly computed
commitments under the selected setup/key and coordinate mapping. The adversary
controls round messages and opening replies, but does not choose unrelated
commitments or the key. Outside the actual joint false-opening event, committed
acceptance implies direct-terminal acceptance; the conditional bound is
`2n/|F| + ε_open`, where the assumed opening bound covers both adaptively reached
queries in that same experiment. A union bound requires no independence.

Tests with adversarial commitments or keys remain useful native controls, but
are outside this first theorem. Security for arbitrary advertised commitments
requires an additional connection/extraction argument with a precisely stated
adversary and setup model; honest-commitment evaluation binding does not provide
it. Record that as a separate research obligation before advertising that stronger
property. Neither the selected upstream scheme assumption nor its stronger
instantiation is established by the direct-library tests.

Reopen a design when an actual client or counterexample violates one of these
contracts, rather than starting another undirected closure cycle.
