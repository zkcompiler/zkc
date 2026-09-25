# Authored interactive protocol compilation

The interactive path compiles a common protocol into independently executable
participants. Local algorithms remain explicit bodies, communication remains
explicit actions, and physical lowering selects an installed backend contract.
The [pipeline](protocol-pipeline.md) owns the architecture; this guide describes
the source-to-participant path and its assurance boundaries. The
[finite table path](table-execution.md) remains a separate tested implementation.

Under the [carrier decision](carrier-consolidation.md) execution uses explicit
`/1` carriers with explicit operation bindings, and BLS profile text is
normalized at the frontend.

## Source, participants and physical execution

The authored [two-factor argument](../../examples/protocols/two-factor.pir)
commits to two original multilinear tables, calls a Sumcheck child for its public
number of rounds, calls the same opening child twice, and checks the product of
the two opened values against the terminal claim. These are ordinary local
algorithms, messages, loops and child calls. There is no whole-prover kernel.

Its source module declares local function bodies, common protocol bodies,
dependency interfaces, selected instances and entries. A protocol owns the
interaction and role-owned ports. A local function owns one participant's
algorithm and has explicit arguments/results. An instance fixes public natural
parameters, dependency instances and the formal-to-actual role map. Dependency
interfaces can require named child parameters to equal named parent parameters;
formation checks their concrete agreement before projection.

| Form | Representation | What remains visible |
|---|---|---|
| Common protocol | `pir.protocol`, `pir.instance`, local `func.func` bodies | Both sides of each message, role ownership, child dependencies, common loops and local algorithm calls |
| Independent participants | `pir.participant`, local calls, send/receive actions and participant calls | One role's values, actual selected child roles, pending ingress, its own local effects and failures |
| Physical participants | Participant control plus `plan.kernel` and `plan.data` | The selected backend, value representation, operation contract and codec; control and origins remain explicit |
| Execution | Admitted immutable artifact, Rust `Runner`, installed backend and transport | Actual resource state, public bytes, limits, suspension and returned/stopped outcomes |

The explicit binding format is a bounded interchange format. The implemented
[text notation](../language/reference.md) provides readable authoring over the same
records, with exact JSON normalization for the Rust host and Lean checker.
Actual MLIR import, projection, physical selection and export are separate
operations. Physical selection resolves installed implementations, including
Arkworks, Dalek and Plonky3, per operation binding. Explicit choices and default
representations are described in [operation bindings](../spec/profiles/source/operation-bindings.md);
this selection is not automatic plan search.

Projection filters foreign arguments and results, resolves selected child
participants, and preserves common public iteration. Each child instance and
role has one definition, shared across repeated calls. Invocations acquire
distinct call and iteration origins. A participant's environment never contains
the other roles' private values.

An owned syntactic stop performs the owner's stop request. A foreign syntactic
stop projects to a distinct incomplete leaf, without reporting that foreign
role's stop site or reason. A dynamic failure inside erased foreign work does
not silently stop an independent participant that still has a local continuation.

## Compiler and runtime responsibilities

The C++ compiler owns MLIR values, definitions, symbols, formation and conversion.
Registered operation contracts check types and symbol uses; whole-module
admission additionally checks ownership, captures, affine use, declaration and
instance closure, schemas, public parameters, stages and limits. Export reads
the actual converted SSA body. MLIR's normalized operation properties are the
input to these checks; textual MLIR is not a byte-identity source format.

Rust owns artifact admission, resumable participant execution, backend services,
resource custody, codecs and the host driver. A runner owns one role and one
backend. Polling exposes a stable local action, send, receive, return or stop.
The host must explicitly advance actions and deliver admitted packets. It cannot
advance a role by supplying a peer's completion flag.

The source-cut driver traverses the retained common source to select local calls
and messages in reference order. Arithmetic runs only in the compiled role's
local body. Delivery encodes using the sender's public codec and decodes under
the receiver's installed policy. Packet envelopes bind the profile, host session,
entry, executing instance, call/iteration path, site, schema and both roles.
Joint-driver cancellation after failure is an explicit host action; independent
roles retain their own continuations and observations.

Native capacity counters and reference work are separate budgets. For example,
the native runner permits 100,000 protocol calls per role; the source reference
charges those calls to its work ledger without a separate call counter. A run
may therefore exhaust native capacity while the reference returns. Differential
agreement within both budgets does not establish equal capacity boundaries.

Participant formation can also admit an
[authored supplied participant](../../examples/protocols/supplied-participant.json).
That route has no common-source correspondence claim and cannot construct a
source-cut schedule without separately checked source custody.

## Admission diagnostics

Compare the admission phase and stable leading reason, not complete message
strings. Location and operand/type details may follow that reason. For the
shared single-defect regression corpus, independent readers agree on:

| Reason | Meaning |
|---|---|
| `interactive-resource-reuse` | A local affine operand was already consumed or returned twice |
| `binding-operation-signature` | Operation input types or arity do not match its binding |
| `interactive-kernel-parameters` | Operation attributes have an invalid shape |
| `interactive-constant`, `interactive-index` | A field constant or curve index exceeds its admitted range |
| `noncanonical-natural`, `expected-natural` | A numeric string has leading zeros or is not an unsigned decimal natural |
| `binding-type` | A carrier type cannot be decoded; native variant details follow this prefix |
| `binding-resource-unit-domain`, `binding-implementation` | Invalid nominal slot or unauthorized implementation selection |
| `local-terminal-context`, `local-terminal-outputs` | Wrong region terminal, or outputs declared when every arm stops |
| `local-if-yield`, `local-match-yield`, `local-yield-types`, `function-return-types` | Incompatible branch results, loop yield or function return |

C++ and Lean admit common source; all three admit the corresponding physical
participants. Rust error categories remain available alongside the leading
reason. A well-formed changed candidate can pass formation and then fail
source-to-plan correspondence (`source-local-unmatched`); forwarding the Lean
checker refusal is not an independent native correspondence check. Raw kernel
APIs, execution faults and dialect-specific errors have their own boundaries.
The corpus does not impose a global first-error order on inputs with multiple
defects. See [current verification coverage](../status.md#3-what-is-checked-and-how).

## Input-selected families

A bounded instance parameter can be selected from actual role inputs:

```pir
instance Main: Family {
  parameters (rounds = ingress(10, P = Select(pn), V = Select(vn)));
  roles (P = P, V = V);
}
```

`Family` declares `parameters (rounds)` and uses `rounds` in an ordinary counted
body. `Select` is a stored local function returning `index`. Its explicit ordered
arguments must be duplicable entry ports owned by the selected role. Unlisted
witnesses and capabilities remain available to the body. Each role executes its
own selectors in lexical parameter order before the body, retaining backend
effects even on failure;
a result above the ceiling refuses. The ceiling itself is at most 1048576; the separate runner iteration budget is
100000, so admitted counts may exhaust deployment capacity.
The joint source-cut driver checks equal selections before interaction; it does
not substitute the prover's metadata for the verifier's. Independent role
runners expose their own selected parameters without assuming peer agreement.

Common and participant MLIR retain the symbolic count and structured selector
binding. Projection preserves one stored loop; actual count zero, one or many
does not change the compiled artifact. The common carrier parameter binding is
`[name, ["ingress", ceilingDecimal, [[actualRole, function, [inputNames...]], ...]]]`.
Projected dynamic counts are `["parameter", name]`; fixed counts retain their
previous encoding. C++, Rust and Lean independently admit the changed carrier.
Port binding names survive MLIR export/renaming together with their selector
references. In MLIR selector functions are `FlatSymbolRefAttr` references, so
ordinary symbol discovery and renaming apply. Dialect symbol-use verification
checks binding structure and selector signatures/roles. Selector types, ownership,
duplicate/missing bindings, count bounds
and unsupported contexts fail closed.

This implementation supports entry families without protocol dependencies.
Calls into dynamic child instances and dependencies from a dynamic instance
refuse. Local helper calls and local algorithm control remain available.
The generic artifact-bound Fiat–Shamir constructor reports
`construction-family-input-required`; symbolic resource provenance and external
construction synthesis are not inferred. Explicit external transition functions
can be called normally. Family participants currently require the full participant bundle even when a
host runs only one role. Selectors must name stored local functions; generic or
configured selector names are not automatically elaborated, and diagnostics come
from PIR admission. The semantic family model is broader than this gate.

The maintained [input-family fixtures](../../tests/fixtures/input-families/counted.pir)
include actual BP+ commitment/L/R byte-length checks for all 1–16 aggregation
sizes, OpenVM optional-shape metadata, and a witness/RNG case. These validate
compact control and admission, not complete cryptographic algorithms. Native
execution is compared with the independent Lean common-source interpreter.

Admitted ingress failures yield stopped runners with an `ingress.<parameter>`
origin, actual backend state, attempted selector actions and earlier successful
selections. Structural input admission still uses `LoadError`. The host's
`ingress[role]` report retains events, selected parameters and that role's reached
stop; `usage[role].external_work_spent` retains native primitive work. Selectors
may call external data operations and consume this work despite having no affine
capability argument. Failed ingress starts no member body or wire communication.

Native roles finish their independent ingress during runner construction. The
Lean joint reference uses the same lexical role order and per-role parameter
order, with each role's ingress iterations charged to its own subsequent body.
Both check count agreement after successful ingress. The reference stops at the
first role-local preparation fault; the native host constructs peer runners
before inspecting stopped ingress. Peer event prefixes on this failure path
therefore need not match. Open-role and reached-role comparisons do not establish
arbitrary joint trace identity. Native host capacity/work and Lean logical events
are distinct evidence.

## External construction execution

Nine `external.monero.*` and `external.openvm.*` contracts use ordinary local
kernels and fixed native provider bindings. The [external transition contract](../spec/realization/external-constructions.md)
owns exact state, grouping and ordered refusal. The [backend API](../../crates/zkc-backends/README.md#external-construction-and-representation-adapters)
owns work limits and installed implementations. Internal artifact-bound
Merlin/Spongefish construction remains a separate path.

Lean independently admits the source and physical carriers and interprets hash
grouping, duplex cursors, extension coefficient order, masking and witness checks.
Only scalar hashing and the 16-word Poseidon2 permutation use replies keyed by
version, exact input and source location. Missing replies yield
`pending-primitive`; malformed or unused replies refuse. The maintained compiled
schedules compare all archived native checkpoints and bounded Lean schedules.
This does not prove those cryptographic primitives, native resource refinement,
automatic external construction, or complete BP+/OpenVM security.

The [attempt adapter](../../crates/zkc-tools/README.md#compiled-attempt-bodies)
keeps typed messages private until returned completion and a selected external
codec. Protocol retry preserves actual RNG/work successor state. Grinding uses
a separate persistent candidate provider and work budget over transcript clones;
only a selected witness is checked on the live transcript. These adapters retain
bounded failure evidence and do not imply eventual success or publication.

## Real backend boundary

`zkc-arkworks` wraps arkworks 0.6 field arithmetic and multilinear commitments.
`zkc-backends` implements the runtime operation, value and resource interfaces.
The production challenge service uses OS randomness. Deterministic tapes belong
to test-only features. zkc does not implement its own pairing cryptography.

Logical table coordinates remain high-half-first. Immutable originals are
permuted once into arkworks' low-bit storage; the challenge vector is unchanged.
Folding allocates scratch and preserves originals. The maintained Lean
coordinate theorem proves the mathematical permutation identity; actual native
tests connect this convention to the external helper.

Commit returns a public commitment and a private immutable opening state. The
state retains the actual original, selected key and commitment state. Open takes
that state and the reached point as explicit operands. It can be borrowed by
multiple child calls but cannot be transmitted or reconstructed from an alleged
wire identifier. No backend-global pointer cache decides which table was
committed. Shared backing is conservatively charged by the runtime, including
spare table allocation capacity.

Public proving material now has bounded persistent transport in
[`zkc-arkworks`](../../crates/zkc-arkworks/README.md). Import requires an
independently expected full-material fingerprint and an actual admitted verifier
key. It checks exact arity, canonical subgroup-checked points, generators, material
identity and the reconstructed setup identity. Fixed row lengths come from the
admitted arity; hostile vector lengths never reach an upstream key deserializer.
This carries no witness or opening state. Matching material and setup hashes
establishes byte association, not an honest ceremony or algebraic consistency
of an arbitrary supplied SRS. The standalone process example exercises PCS
transport. The [constructed artifact path](artifact-execution.md) now adds
independent proof-file producers/validators over a selected public-artifact profile.

Affine RNG and nonce capabilities have backend-issued identities, owners,
generations and budgets. Entering a local/call/loop frame checks actual argument
aliases and restricts its resource view. Consumes advance authoritative state
before a possible failure. Leaving or cancelling a frame preserves completed
transitions and resources outside its view. Static SSA checks complement these
dynamic checks; they do not prove issuance or authenticity.

The installed key, arity and optional public-input pins are host policy. A
parameter named `n` has no implicit backend meaning. The
[`zkc.run/2` host](../runtime/inputs.md) supports multiple explicit setups,
checked original port names and per-receive setup selection. Other hosts can use
the library API with selected keys and entry policies. Development
setup and local-only public-input checks do not establish production setup
provenance or agreement of arbitrary external statements.

## What the Lean connections establish

There are several distinct connections, with different premises:

| Connection | Meaning and limit |
|---|---|
| Typed source-to-role projection | Direct source-role meaning and a separate target interpreter agree for the maintained typed grammar and stored definitions. This is a structural theorem, independent of a native artifact. |
| Source cuts and open execution | Source-derived prefix alignment and actual local/message cut laws relate joint reference order to independent role cursors. They retain failure effects; they do not equate arbitrary schedules' final states. |
| Restricted resources | Heterogeneous selected views preserve actual returned/stopped effects and outside state, with a consumer on projected stored roles. Native authenticity, alias and generation checks remain separate. |
| Portable candidate checking | A separate executable Lean consumer admits the actual source and candidate and compares projection with alpha normalization and the selected physical contract. It checks concrete artifacts. |
| Native differential execution | Actual compiled Rust execution is compared with independent source/role reference observations over the admitted test domain. This provides implementation evidence, not universal formal equivalence. |
| Committed Sumcheck security | For factors fixed before challenges and honestly formed commitments, the terminal connection reduces false acceptance to Sumcheck failure or a joint bad-opening event, with loss `2n/|F| + ε_open`. |

Raw portable decoding, ownership filtering, multiple results and SSA renumbering
are not proved to elaborate to the typed projection theorem. The concrete
portable checker and differential tests are the current connection to native
code. The security theorem assumes the selected cryptographic opening contract;
it does not prove arkworks internals, arbitrary commitment extraction, setup
authenticity, Fiat–Shamir security or zero knowledge.

The prefix theorem and individual failure-cut laws have not been assembled into
one recursive theorem for the complete heterogeneous controller and global
observer. Native driver evidence is differential testing. The
[executable reference architecture](../../formal/design/interactive-reference.md)
explains the checker/interpreter and separates these results precisely.

The executable source reference uses a symbolic honest PCS service. A proof token
in that service records its issuance point. Actual cryptographic proof bytes
need not uniquely determine that point: an affine-polynomial counterexample
verifies at another point with its correct value. Honest opening-flow comparisons
and arbitrary hostile proof/query tests therefore have different scopes.

## Other clients and extension boundaries

The [group exchange](../../examples/protocols/group-exchange.json) has no polynomial
operations. It exercises explicit interaction and consumed nonce state under a
real Arkworks BLS12-381 G1 implementation, with no group cryptographic security
claim. [Construction and artifact execution](artifact-execution.md) is a separate
consumer of admitted source. Neither route implements a full execution-proof
argument, a complete zkVM or recursive verifier generation.

## Ordinary local storage lifetime

`protocol-compile` and `protocol-physical-ir` accept opt-in `--release-storage`.
The equivalent participant planning option is
`--zkc-plan-participants=release-storage=true`. Physical selection runs first;
then C++/MLIR computes each value's last SSA use in each admitted one-block
`func.func`. This applies to retained local definitions, including definitions
that no participant reaches. It does not analyze participant environments,
callers' lifetimes or unused function outputs that escape to a parent.

The pass emits typed `plan.release` with physical data operands and no results,
site, attributes, purity or speculation traits. The portable ordered instruction
is `["release", [names]]`. The typed source carrier has a separate `Release`
variant; only physical participant local bodies admit it. Common and logical
source, generic definitions and participant control reject it. Release has no
mathematical operation contract and cannot select a backend implementation.

Unused discardable arguments release at block entry, after local frame admission
and successful argument retention in the runner. A zero-use discardable result
releases immediately after its producing kernel; otherwise release follows its
last consuming kernel. A return is a use and prevents release. Releases at one
position group values in argument/definition order, with at most 1,024 operands
per release. Existing artifact byte, instruction and port limits still apply;
a candidate enlarged beyond them refuses admission.

Only admitted immutable local values can release, including internal views,
prover/verifier keys and private opening-state custody. These permissions are
independent of public serialization: private custody still has no public wire
codec. RNG, nonce, transcript, capability and unknown opaque kinds cannot
release. The installed value adapter must provide inert destruction and stable
retained-size accounting for every admitted releasable kind.
C++ and Rust independently retain definition identity and mark released values
unavailable. Later reads or returns, rebinding, duplicates, unknown names and
empty releases reject. MLIR additionally checks every SSA use precedes release
in the same block. Lean independently checks the actual ordered body, including
resource exclusion and availability, before erasing releases for exact source
correspondence. Erasure alone is not an admission procedure. Existing diagonal
representation checks still require a real contraction use.

The runner removes only its local environment reference. It performs no backend
callback, authority mutation, instruction tick or operand/result observation for
release. Every original kernel and site, operand/result observation, instruction
tick and logical charge remains. Two scalar ghost counters record the count and
exact bytes of every successfully retained local binding. These charges survive
physical release until function exit, including early failure. Kernel output
budgets therefore use the same logical live and cumulative charges, and shared
Arc backing remains charged once per retained binding as before. Function exit
subtracts the complete local ghost ledger; failed retention adds no entry.

The trusted value adapter requires stable type/size, cheap nonpanicking cloning
and inert nonpanicking destruction of discardable immutable values. No claim is
made for external value implementations whose destruction changes semantic
state. Shared backing remains allocated while another local, parent, result or
backend reference owns it. Logical charged bytes are not resident memory. This
pass eliminates no allocation or kernel and promises no universal RSS or latency
reduction.

`PhysicalOptions.releaseStorage` selects the same pipeline in the compiler CLI
and claim-lowering checker. The checker recomputes from the checked construction
and compares the actual candidate while retaining caller source and authority.
Combining storage release with another physical selection does not strengthen
that selection's resource-equivalence contract. The standalone storage change
has exact accounting tests; diagonal selection retains its separate limits.

The [abstract local storage law](../../formal/Zkc/Compiler/Storage.lean)
proves release erasure by evaluator induction. Environments agree on backward
needed variables; opaque effectful kernels receive equal operands and logical
state. The theorem retains exact errors, post-failure state, ordered events,
logical charges and cleanup on both success and failure. It does not assume
kernel purity or successful execution. Return operands participate in liveness.

The independent tool formation/correspondence checks and executable physical
reference are implemented. Connecting those checks to the theorem's `Safe`
predicate, instantiating its policy with the native runner and composing full
participant executions remain separate realization obligations. The theorem
models mathematical allocation success or matched allocator outcomes. Earlier
physical deallocation can change native allocation failure, so native OOM,
fragmentation, timing and RSS are not equated. Backends must not observe addresses,
map ownership or Arc reference counts. Exact logical policy exhaustion is still
covered; it is not weakened to a sufficient-budget-only statement.

Release-specific diagnostics follow the selected compiler string-ID convention:

| Diagnostic | Refusal |
|---|---|
| `interactive-release-context` | Release outside a physical one-block local or with a site |
| `interactive-release-shape` | Wrong portable release arity |
| `interactive-release-empty` | Empty release list |
| `interactive-release-unavailable` | Unknown, duplicate or already consumed/released value |
| `interactive-release-resource` | Resource or opaque storage selected for release |
| `interactive-release-live` | SSA use after release or outside its block |

Portable later reads use the existing `interactive-resource-reuse` availability
refusal; rebinding and port limits retain their existing diagnostics. Rust uses
its existing `Ssa`, `Type`, `Record` and stage errors. Lean retains independent
`release-context`, `release-empty`, `release-resource`, `release-unavailable`
and operand availability checks.
