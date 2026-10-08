# IR foundation

This document defines the selected scope and completion criteria for the native
IR foundation. The [validation map](foundation-validation.md) records its
completion evidence. It is not an expanded admission specification.
[Status](../status.md) owns current support;
[the roadmap](../roadmap.md) owns sequencing. Exact operation contracts are refined in
`docs/spec/` before their implementation. The [native proof profile](../spec/profiles/compiler/native-proofs.md)
now fixes the independent execution and construction boundaries; the
[proof execution guide](native-proofs.md) and [migration baseline](migration.md)
record scope and remaining consumers.

## Objective and completion boundary

Complete the general mathematical IR and its compiler/runtime realization.
Protocol examples expose requirements and test combinations of features. Full
protocol-library migration and external prover/verifier compatibility have their
own milestones; they are not foundation completion conditions.

The existing `protocol → participant → exec → physical` profiles remain the
architecture. Direct MLIR and source programs exercise the foundation. The fresh
frontend is implemented; native Lean and remaining consumers follow the
[migration roadmap](../roadmap.md#next-package-native-lean-connection).
The long-term migration still preserves existing features, libraries and checking
obligations; changing this milestone does not remove those obligations.

### What general execution means

A protocol author supplies an algorithm as an IR program, together with declared
inputs and primitive contracts. Within the selected executable profile, its legal
combinations of operations, regions, calls, values and effects must use the
ordinary projection, lowering and runtime. Adding another such program must not
require a compiler branch on its protocol name, a new executor, or a hidden
whole-prover/verifier implementation. A genuinely new mathematical primitive can
require a reusable operation, lowering or backend installation.

Logical type formation alone does not establish executable support. A selected
execution profile also needs compatible representations, region/call handling,
resource flow, input constructors, message codecs and installed kernels. State
these limits explicitly and test compositions across those boundaries. Missing
support inside the selected scope is a foundation gap; writing another algorithm
with already supported features is protocol authoring. External file/proof formats
and application deployment adapters belong to their own compatibility contracts.

Independent noninteractive proving and verification remain foundation checks.
Representative constructed and authored programs use the common interpreter in
separate processes. The verifier needs its authorized public context and proof,
without a live prover, witness or shared prover state. Existing complete Schnorr
and Sumcheck clients retain their regression role. New component tests must
finish and check their declared computations, effects and failures; an isolated
operation test or a replay alone cannot establish compositional execution.
General network transport and Rust code generation remain later work.

The [roadmap](../roadmap.md#completion-milestones) distinguishes foundation
completion from full migration. The [migration inventory](migration.md) retains
frontend, Lean/checking, table and public-consumer obligations.

### Three kinds of coverage

| Coverage | Foundation evidence | Separate claim |
|---|---|---|
| Representation | Source-backed requirements from contrasting protocols map to typed operations, shapes, control and effects, including their combinations | A mapping does not claim that a whole protocol has been authored |
| Execution | Representative composed IR programs compile and run through shared machinery; independent references check their actual results, state and failure behavior | Component coverage does not claim complete BP+, Groth16 or zkVM execution |
| Compatibility | Preserve existing external contracts on their current paths; a chosen generic codec or primitive test checks its exact byte contract | Full library migration and snarkjs/Monero/OpenVM interoperability are separate work |

## Protocol corpus and structural requirements

Use these protocols to discover missing abstractions and test generality. No row
requires a protocol-specific dialect, pass or executor. A structure discovered
here must have an explicit owner, an implemented generic realization and a
composed executable test before its foundation requirement closes.

| Protocol reference | Structure the IR must retain | Foundation checks | Separate protocol work |
|---|---|---|---|
| Schnorr/DLEQ | Blinding, actual receives, affine nonce/transcript state, final equations | Retain complete constructed/authored regression clients; mutate receives, guards and resource aliases | Wider protocol libraries and security analyses |
| BP+ | Range reduction dependencies, group/vector folds, padding, dynamic shrinking state, partial inverses and whole-attempt retry | Map the actual algorithm's structural needs; execute group/vector folding with transcript and affine state, partial failure and persistent retry; use a contrasting stateful client | Full range prover/verifier, complete equation reference and Monero wire compatibility |
| Groth16 | R1CS/assignment schema, QAP/domain computations, G1/G2 MSM, pairing, keys, randomizers and typed proof data | Map the algorithm to general operations; execute composed bulk-algebra, key and heterogeneous-message cases, including an authored noninteractive path with no imposed transcript | Full native Groth16 library migration and BN254/snarkjs depth-2/16 comparisons |
| Pairing target-group composition | Pairing results as typed group values, scalar action, equality, messages and carried state | Execute a small value-producing pairing and target-group computation with canonical input/message checks and a contrasting algebraic client | Full pairing-based commitment/reduction libraries and prepared-key compatibility |
| Sumcheck | Formal polynomials versus tables, axes/degree, shared factors, received coefficients, dynamic rounds and terminal composition | Retain public and committed-original clients; vary rounds and mutate terminal points/subjects; reuse their operations in other programs | Broader Sumcheck libraries, PCS schemes and cryptographic proofs |
| R1CS execution proof | Relation/program identity, trace/witness inputs, reduction calls and terminal bindings | Compose relation computations with reductions and an actual terminal; vary program/input/assignment and check binding failures | Complete existing machine-client migration and larger ISA coverage |
| AIR and lookup | Multiple traces, extension embeddings, rotations, lookup/permutation structure, quotients, batching, authenticated queries | Map the required computations and run composed trace/constraint, opening/query and mixed-shape cases; check invalid authentication and optional data | Full AIR/lookup argument libraries, FRI client migration and production proving |
| OpenVM | Optional heterogeneous AIR data, layer/received arity, fractional Sumcheck/GKR, stacked reductions, WHIR/query/grinding state | Trace the pinned implementation's structural requirements to IR owners and generic executable cases; distinguish absence/presence and trial/live state effects | Full upstream prover/verifier, recursive stack and external proof compatibility |

Mapping an operation name is insufficient: include input/output types, control,
state, byte boundaries and combinations with neighboring stages. A required
structure with no implementation or composed test leaves foundation work open.
Deferring a whole protocol does not defer a core requirement discovered in it.
The corpus validates a declared scope; it is not evidence of universal protocol
expressiveness or cryptographic soundness.

When a complete BP+ library is later implemented, select its paper revision,
group, range width, padding, transcript and challenge policy. Existing
Bulletproofs/IPA clients do not establish BP+ algorithm coverage. The structural
mapping and generic tests still use the actual BP+ requirements now, rather than
assuming that a scalar fold covers group/vector, retry and padding behavior.

### Using the corpus to choose abstractions

Use the clients throughout design and implementation. For each proposed core
mechanism, record its exact need, existing representation, smallest extension,
contrasting consumer and a counterexample that would reopen the choice. Reuse
ordinary SSA, regions, symbols and operation interfaces before adding a new
construct. A protocol's name is not a reason for a dialect or executor.

Schnorr/DLEQ first exposes construction and observation boundaries; committed
Sumcheck with PCS tests the same path across rounds and terminal openings.
Groth16 is the contrasting already noninteractive client and must not acquire
an artificial interactive or Fiat–Shamir stage. BP+ and AIR/OpenVM components
exercise changing shapes, persistent state and composition. Retain a three-role
communication/service control so the common model is not accidentally binary.

Vary round counts, aggregation sizes, empty/optional components and received
values. Also vary alias bindings, reused versus newly drawn values, stopping
prefixes and later disclosures. Select controls by the boundary under review;
do not require every combination for every protocol. Track expression, execution,
external compatibility and analysis applicability separately. A complete client
may be outside an affine analyzer's chosen fragment without exposing an IR gap.

Use focused examples to diagnose a boundary and composed programs to test its
interactions with other features. Existing complete clients remain regression
controls. New full protocol implementations are useful optional evidence; the
foundation gate is coverage of the general requirements above.

## What belongs in the foundation

| Area | Implement or stabilize now | Can follow without redesigning the core |
|---|---|---|
| Values and shapes | Typed immutable aggregates, empty data where meaningful, dynamic extents, nested containers, nominal identities and checked shape relations | Broad dependent types, higher-order authoring and new containers without a client |
| Mathematics | Transparent vector/matrix/field/group/pairing operations; formal polynomials, domains, ordered axes, residuals and extension embeddings needed by the clients | New mathematical theories and domain installations through the same contracts |
| Structured computation | Compact bounded maps/folds and local branches/loops, correct captures and per-result dependencies | Parallel/fused execution and general recursive functions |
| Interaction | Compact counted protocol regions, carried role values, actions and services; static applications inside regions; input-selected configurations | Arbitrary private distributed choice, dynamic participant creation, runtime higher-order protocol calls |
| State and effects | Explicit randomness, nonce/transcript ownership, service aliasing, stops, cancellation, attempts and retained work | New service implementations; concurrent scheduling with separate justification |
| Relations and terminals | Structured immutable relation signatures, imported identity/purposes, executable relation computations, actual residual/opening bindings, setup/key/config associations | General automatic security analyses or arbitrary relation solvers |
| Realization | Complete typed primitive contracts, representations, codecs, bounded native kernels, structured lowering and accounting | Faster kernels, GPUs, bufferization/fusion and new physical representations |
| Construction and proof execution | Authored transcripts and selected native derivations, independent role execution, authorized public context and complete proof I/O | Broader automatic construction and new cryptographic security theorems |
| Extension and checking | Body-derived dependencies and bounds; exact semantic admission; source/candidate identity, provenance, observation inputs and checker applicability | Affine observation and other rich algebraic analyses, property transport automation and broad new Lean proofs |

Existing functionality needed by these rows moves now at the IR/runtime level.
User-facing source syntax and package ergonomics have their own
[implemented profile](../spec/profiles/source/mathematical-language.md). A postponed
consumer gets a destination and preservation obligation; it is not erased from
the overall migration inventory.

## Representation and dialect responsibilities

Keep one mutable mathematical program in MLIR. SSA edges express value
relationships; regions express actual binding/control boundaries; symbols express
reusable definitions. Derived analyses may cache facts for an IR revision but
must not become another editable mathematical compiler.

| Owner | Responsibility |
|---|---|
| `protocol` | Roles, communication, service cuts, statements, composition, coordinated iteration and projection |
| `local` | Ordered participant computation, partial operations, local control, affine ownership and stopping |
| `algebra` | Field/group/pairing meaning and domain-specific bulk algebra |
| `poly` | Formal polynomial meaning, degree/axes/domains, evaluation and residual operations |
| `relation` | External relation schemas/assets, trace/constraint meaning and explicit input purposes |
| `crypto`, `pcs`, `oracle` | Their declared cryptographic primitives, transcript transitions and commitment/query contracts |
| `plan` | Physical representations, kernels, storage and execution choices |
| Builtin/`tensor`/`scf` | Reused type, aggregate and structured-computation machinery where the admitted semantics match |
| `data` | Domain-independent products, sums and runtime-count nested sequences; numeric tensor arithmetic retains its existing owners |

The `data` dialect owns common record/variant construction and access, while
numeric arrays use builtin ranked tensors and their mathematical owners.
No protocol-specific dialect, universal `proof` dialect or mandatory `compute`
wrapper is selected. Flat scalar SSA remains useful inside structured regions.
Existing independent finite/reference owners remain until their consumers have
an explicit disposition.

### Aggregate and shape contract

Prefer ranked tensors with dynamic extents for homogeneous immutable data when
the element semantics fit. Products and variants retain nominal/structural
identity; they are not flattened into untyped byte arrays. Fixed rank with dynamic
length is sufficient for shrinking vectors without a new type at each iteration.
Ragged AIR data needs a bounded sequence of individually shaped rank-two
trace tensors. Builtin tensors cannot directly contain builtin tensor elements.
The [nested-data profile](../spec/profiles/compiler/nested-data.md) selects an
explicit sequence after comparing tensor wrappers and parallel numeric arrays
against opening batches and ragged-matrix clients. Nested
heterogeneous proof structures use typed products/sums and bounded sequences.
Absence is an explicit variant, not a fake zero element. Upstream tensor formation
accepts dialect element types, so group elements alone do not require another
container. Admitting and lowering those elements still requires zkc contracts.

Availability is whole-value and conservative. Components with different
owners use separate SSA ports or an explicit structural contract; packing a
private leaf cannot make it public. Affine values remain single-owner and cannot
be hidden in copyable containers. Branches consume only the active payload;
zero-trip loops return their initial carried resources.

The structured profile uses canonical ranked tensors and the nominal
variant ABI; the [structured-value contract](../spec/profiles/compiler/structured-iteration.md)
owns exact mappings and exclusions. Existing vector/matrix backends provide the
storage. Static arrays retain distinct type/codec identity. Optional matrix
products and runtime-length nested aggregate sequences execute. Sequences
retain their distinct recursive storage, ownership and wire contracts.

An operation is total only when its preconditions follow from admitted static
facts or checked facts retained at the right boundary. A dynamic tensor index,
shape cast, equal-length zip, nonzero inverse or domain conversion is not total
because MLIR accepts it. If a precondition is not established, use an ordered
checked local operation with a defined stop, or refuse. Guards are not freely
hoisted to entry; their timing and reached state matter.

Dynamic collection shape and polynomial arity are different problems.
The polynomial profile uses a closed formal ring recipe plus ordinary factor-table
state and an accumulated prefix. [Polynomial recipes](../spec/profiles/compiler/polynomial-recipes.md)
define the degree and observation equations. Checked local realizations keep one
carried type while factor arity changes. Nested Sumcheck layers derive their inner
arity from received outer induction, so no fixed ambient rank or padding is
assumed. This covers that discrimination case; it is not a complete GKR verifier.

The alternatives were a fixed ambient formal value with a prefix, and a new
runtime formal-polynomial type with dynamic arity. The first cannot directly
represent received layer-dependent rank without an embedding contract. The
second would duplicate the existing concrete factor storage and add a runtime
expression ABI. Retaining the finite recipe at compile time and generating its
checked operations avoids both costs. The state does not attest lineage; verifier
terminal equations use original subjects or separately checked openings. Products
remain formal products of MLEs, not MLEs of pointwise products.

### Three distinct control meanings

1. **Total computation:** bounded transparent regions for map/fold and admitted
   pure branches. Captures, bounds, yields and all possible selected operands
   enter dependency analysis. Unordered reduction needs an explicit associative
   law; an ordered fold does not acquire one from purity.
2. **Local execution:** retain `local.for`, `local.if` and `local.match` for
   stopping, accounting and affine work. Their current contracts differ from
   unrestricted upstream `scf` speculation and index behavior.
3. **Protocol iteration:** `protocol.repeat` is the implemented common operation.
   Its isolated body carries role values and captures explicitly and projects
   to executable `protocol.loop`. Executable programs retain received and
   iteration-derived counts, maximum bounds, services and occurrence paths.
   The [iteration profile](../spec/profiles/compiler/structured-iteration.md)
   owns these semantics. The older named-parameter loop grammar remains a
   separate migration consumer.

Use MLIR region/call/symbol interfaces where their semantics fit. Upstream `scf`
can serve admitted total/local lowering; it does not establish that different
participants know the same count or choose the same branch. Regions require
region-aware dependency, availability, degree and ownership analysis; direct
operand summaries alone cannot cover captured values or loop feedback.

A value available at P and V denotes two components, which can differ. This also
applies to iteration counts: a joint invocation checks the components of roles
participating in a segment for equality under the declared agreement contract,
before starting that segment. This does not imply equality of their carried data.
A joint invocation may similarly validate role-local selectors/configurations. An open participant still runs from its own actual inputs;
that host check is not implicit communication or a soundness assumption about an
adversary. Preserve ingress effects and failure order. Only shape checks proved
safe to move may run earlier.

Foundation interaction uses a bounded configuration selected before the relevant
schedule begins. Optional components use explicit selected configuration and
structured iteration/choice with known role views. A received or iteration-derived
count may determine a later segment's count/schema if it is available before that
segment, bounded by a static or entry maximum, and checked at a declared boundary.
Earlier challenges do not invalidate this rule. Arbitrary private communication
branches and schema changes inside an already-started segment remain outside the
initial contract. A required client needing those features reopens this boundary;
it cannot be encoded as invisible host control.

A zero/one count is already a restricted distributed choice. The agreement
contract therefore covers presence/absence as well as larger counts. Classify
count provenance as entry-derived, received, or iteration-derived, with a checked
per-role upper bound before the affected body starts. A later received count needs
an explicit validated segment boundary; ordinary entry selection cannot justify
it. Mismatched open participants retain their distinct outcomes; the joint driver
reports its declared mismatch/pending/decode outcome without inventing a global
protocol rejection. Each role executes its own reached ingress/decode/bound checks
before the joint agreement check for that segment; preserve those local outcomes
and effects. Agreement is a separate driver observation, not a substitute for a
verifier's validation. Include a mutation where the verifier's bound check stops
before the driver could report mismatched counts.

Availability on carried values needs a conservative loop invariant/fixed point,
including the zero-trip path. Exact resource identity needs more than a union of
possible origins (a loop swapping two roots depends on count parity). Check both
separately. Body-only total expressions are demanded at an actually reached body
consumer; zero iterations do not execute that work. Initial carried results still
need their values if returned. Ordered operations already executed before a loop
remain executed. Extend the lowering postcondition with per-body/capture/carried
anchors before permitting code motion. Do not enable LICM or speculation merely
because an operation implements a loop interface.

Logical sizes retain checked natural-number meaning. Using tensor dimension/slice
operations requires an admitted `index` fragment. Checked per-iteration shape
operations, such as exact halving, enforce the current contracts without a general
shape-invariant analysis. Carried ports may have different
role sets and both growing and shrinking dynamic extents. Machine `index`, overflow
flags, division, shifts and tensor casts require an explicit admitted lowering;
upstream verification is insufficient. Re-admit folder-created constants and
other results under the closed vocabulary or prevent that fold, rather than
rejecting an otherwise supported program after uncontrolled canonicalization.

Compile-time expansion of an acyclic application inside a loop is acceptable if
it expands the body once. Runtime size must not multiply stored IR size. Genuine
residual results are SSA arguments to subsequent components. Resource/service
substitution preserves exact root identity; the union of possible roots is never
ownership evidence. Preserve distinct occurrences across nested calls/iterations.

### Primitive and mathematical boundaries

Keep arithmetic, MSM, polynomial transforms and pairing meaning inspectable as
named mathematical operations or transparent reusable bodies. A backend may
implement these operations efficiently under an exact contract. It may not hide
all of Groth16, BP+ or Sumcheck in one custom operation to satisfy the corpus.
Existing `local.func` bodies can be reused when their ordered execution contract
still applies and their contents remain inspectable. They cannot serve as a hiding
place for all mathematical structure needed by an analysis. An opaque leaf cannot consume the target client's witness and produce its whole
proof, or consume its proof and return the whole verifier decision. List each
admitted leaf with its exact mathematical/effect contract under its existing owner;
review its inputs, outputs and the stages it hides. Declared PCS/oracle primitives
below are explicit boundaries, not permission to wrap a complete corpus client.
The common Rust interpreter is the selected execution target. The existing
Python carrier evaluator remains bounded independent compiler-test support;
there is no new whole-foundation reference interpreter. Reuse independent
primitive/equation references and actual generated-runtime controls. See the
[runtime design](../runtime/design.md#current-execution-architecture).
Generic PCS/oracle commit/open/check operations can remain declared primitives;
the surrounding batching, queried points, claims and verifier checks stay visible.

An extension supplies logical identity, domain/shape rules, result dependencies,
effects or totality justification, realization requirements, and evidence for
claimed laws. MLIR `Pure` or an interface attached to an unknown operation grants
no admission. Start with explicit per-owner admitted models; do not build a
user-pluggable theorem engine. Existing checked source-library functions later
elaborate to transparent definitions or declared local contracts through this
same boundary.

Preserve the distinction between formal polynomials, coefficient vectors,
evaluation tables and virtual/shared-factor representations. Materializing a
polynomial is a realization choice. Degree facts need derivation or checked
premises; a received array of coefficients is not an honest prover polynomial.
Domain order, basis, base-to-extension embedding and quotient preconditions remain
explicit. Partial division has local failure behavior unless established total.
Bulk checked inversion can be one local operation; a nonzero refinement type is
an alternative only if it removes a demonstrated barrier. Groth16's concrete coset
numerator and prepared H-query convention must remain distinguishable from exact
polynomial division. Their correspondence under relation satisfaction is a
separate obligation, not a reason to change unsatisfied-input behavior.

Pairing-product checks and target-group values have different interfaces. The
selected corpus includes a small `G1 x G2 -> GT` computation whose result is
combined, sent and carried through ordinary control. Use the existing group
abstraction if its laws fit, with explicit associated domains, checked subgroup
admission and canonical codecs. Raw Miller-loop state is not a target-group
value. This requires neither a new dialect nor a complete protocol library.

Full cofactor Edwards points are not a module over the prime-order scalar field:
field reduction would make scalar distributivity false on torsion. Keep encoded
bytes, decoded full-curve points and subgroup values distinct, with the exact
allowed actions and explicit checked/clearing maps. This contract and negative
controls belong now even when full Monero compatibility follows later. Hash the
representation specified by the transcript contract; decoding and re-encoding
must not silently replace the original bytes.

### Transcripts, services and execution observations

Authored transcript transitions and selected native transcript constructions
belong in the foundation. The selected [construction placement](native-proofs.md#why-construct-after-projection)
analyzes common source, then emits explicit state into unsimplified participant
mathematics. It adds no role-family join, dialect or IR profile.
General automatic Fiat–Shamir construction and its security arguments remain
later research. Retain absorb grouping/order, byte
encoding, domain identity, sample type/mapping and actual state successors.
An affine live transcript must not become a copyable mathematical expression; the explicitly
copyable external data-state contracts keep their distinct meaning.
BP+ retries rebuild a fresh transcript from the same initial public context inside a whole-proof attempt;
they do not require a generic clone or rollback operation. Existing OpenVM grinding
trials do inspect a clone under their explicit primitive contract, retain consumed
work. The existing [search/caller contract](../../crates/zkc-backends/src/external/README.md#native-integration)
requires one explicit live check of the selected witness. A direct verifier check
retains its state effects even when false, unlike a trial on a clone. Preserve
these contracts without introducing arbitrary affine snapshots. Primitive state
import validates encoding, not reachability or authority to restore a live
capability; it does not justify a general IR restore operation. Keep diagnostic
sites separate from cryptographic labels.

Preserve Monero hash-chain and OpenVM duplex boundary behavior already present
in zkc. For example, sampling zero bits can still consume a draw, whereas the
selected zero-bit grinding check performs no transcript transition. Do not
normalize these by the returned value alone. Retryable challenge failure, fatal
failure, decode stop and resource exhaustion remain distinct. Failed attempts
can discard buffered output while preserving consumed randomness and work.

Service references remain non-wire handles. Static substitution and immutable
borrowed loop ports retain one authenticated root and its sequential state.
The service state advances through each query; the reference itself is not a
selectable/yielded mathematical value. Affine transcript tokens, unlike these
ports, are carried explicitly and consumed/yielded once per live iteration. Dynamic
service creation, exchange and higher-order service selection are not required
without a concrete client.

The `zkc.run/1` bundle carries checked recursive segments over `zkc.program/1`.
Flat and nested bodies use the same execution contract and schedule validator.
Compact IR alone is insufficient: projection metadata, bundle scheduling and
runtime inspection must represent nested iteration and dynamic occurrence paths
without flattening all iterations. The implemented structured schedule/bundle revision
independently checks action coverage, count binding, depth/step limits and
zero-trip behavior. A new control form must not merely bypass the old coverage
check. It interprets structured per-role programs and matches endpoints by static site
plus dynamic occurrence path under compact repeated segments. It stores no entry
per runtime iteration. Per-role validity alone does not establish joint
compatibility: preserve cross-role pairing, causal order, count agreement and
mismatch/deadlock outcomes. General concurrent interactive transport remains
later; independent noninteractive producer/validator execution belongs now.
Finite role count is independent of a two-party crypto example; keep a
three-role communication/service control in the regression corpus.

Native realization must support the corpus without scalar expansion proportional
to every data element in stored IR. Reuse bulk backend kernels and compact loops
before introducing a new performance subsystem. Actual runtime work may scale
with input size and remains bounded. Mathematical formation limits and executable
budgets are separately reported. Performance tuning can wait; a default refusal
of every meaningful required client cannot.

### Information retained for observation analyses

Affine observation research consumes the mathematical subject and an explicitly
selected observer, continuation and set of premises. Preserve the inputs below
while extending or migrating the compiler. This is a design constraint on the
representation and its transformations; implementing the analyzer is a separate
change and is not a new completion condition for current frontend or placement
work. Existing admission and analysis profiles keep their stated scope.

| Input | Retained meaning |
|---|---|
| Algebraic expressions | Typed operands, domains and interpretable definitions for the analyzed fragment, connected to actual draws, receives, guards and outputs; an opaque primitive needs a selected interpretation or remains outside the fragment |
| Randomness and derived challenges | The actual reached operation, owner, service contract, inputs/reply and state transition; distinguish an entropy draw, reuse of a drawn value, and a challenge derived from transcript state |
| Role components | Each sender's expression and each receiver's actual reply remain separate; declared availability establishes neither equality nor secrecy |
| Capability roots and aliases | Entry bindings and call/iteration substitutions retain the root identity or symbolic alias relation and sequential state; a renamed parameter does not create an independent resource |
| Ordered behavior | Message/query/guard/local-stop order, branch and iteration context, and consumed state/work in failed or retried prefixes; include effects hidden inside a local body through that body's interpreted contract |
| Later disclosure | The chosen observer's public inputs, visible messages/results and selected continuation, including later disclosure of masks or correlated values; internal guards, failures and state are visible only as specified by that observation |

A static draw site inside a loop can execute repeatedly or never. Its dynamic
occurrence includes the call/iteration/attempt path, without requiring an
unrolled IR or recording every secret value in a runtime log. Runtime root
bindings may be supplied separately from the artifact; keep their correspondence
to symbolic ports without serializing authority-bearing handles or secret RNG
state. Retaining an analysis input does not make it public protocol data.

Keep an immutable admitted mathematical subject for the selected analysis and
identify its relationship to transformed candidates. Derived analysis views
are revision-bound consumers of this subject, not a second editable graph.
Retain transparent mathematics before lowering and the exact binding contracts
for interpreted local operations. A dependency list alone cannot establish an
affine expression. Transformations preserve the selected observations or require
the analysis and its correspondence to be re-established; a source location or
digest alone supplies neither. Construction creates a new experiment, so an
interactive source judgment does not automatically apply to its transcript
candidate.

Honest delivery is a separate assumption or established channel property.
Uniformity, freshness and independence require explicit provider/initialization
and history premises. Different SSA names, sites, roles, sessions or capability
roots do not establish them; repeated draws from one root are not automatically
dependent either. Alias identity and a probability law answer different questions.
In particular, a Fiat–Shamir challenge is derived from a selected transcript,
not an independent random input justified by placement. A concrete transcript
contract selects framing, domain labels, mapping and state transitions, as
illustrated by [Merlin's operations](https://merlin.cool/transcript/ops.html);
its [private RNG](https://merlin.cool/transcript/rng.html) has additional inputs
and must not be conflated with public challenge extraction.

For example, over a finite field, `u = w + r` with a uniform mask independent of
the secret and the observer's prior information can hide `w` from an observation
of `u` alone. A continuation that also publishes `r` reveals `w = u - r`.
Two outputs sharing one mask can similarly reveal their difference. These are
small retention controls, not security claims for the whole protocol corpus.
Unknown primitives, unresolved aliasing or an unspecified continuation must
remain explicit analysis limitations rather than implied secrecy or freshness.

The existing native [public-coin view](public-coin.md) is narrower: it tracks
selected verifier dependencies and ordered challenge prefixes. It does not
already implement this observation analysis. Use the existing effect and
ownership contracts to preserve draws and stopping behavior; MLIR's
[effect interfaces](https://mlir.llvm.org/docs/Rationale/SideEffectsAndSpeculation/)
support transformation restrictions but do not supply probability or security
laws. No observation-specific dialect or new mutable IR is selected here.

### Relations, origins and future proofs

Relation signatures must admit the required immutable aggregate inputs, including
matrix parameters, public vectors and witness traces. Reuse their logical shape,
domain and nominal identity rules in declaration consistency and entry bindings.
Dynamic dimensions remain parameters of the declared relation where its semantics
allow them; they do not imply a new relation identity for every runtime size.
Affine services and capability aggregates require their own contract and are not
admitted merely by widening this data signature. Keep actual input purposes,
role selectors and acceptance mapping through projection and deployment.

External relation generation can remain external. zkc retains the relation's
identity, schema, ordered purposes, actual data and relevant interpretable
constraints when analysis needs them. A schema label alone proves neither
relation satisfaction nor source-to-relation adequacy. Key/config/relation
associations and actual residual/opening subjects are checked at declared
boundaries; no new trusted-setup protocol is implied. Retain exact interpretation
or asset references when a definition is available. An external identity without
an interpretation remains uninterpreted; it grants no predicate or setup law.
Select any richer definition carrier with its actual analysis/checking consumer.

Retain source locations, symbol and application origins, actual operands,
requirements and compiler settings through the applicable transformations.
The frontend's source-to-IR interface must preserve these contracts without a second
mathematical IR. Locations alone are not correspondence evidence. Existing report
checkers must either cover new forms or reject them explicitly; old proofs and
reports do not automatically apply to richer regions or carriers.

Native Lean implementation follows the frontend exchange design and must
connect to the retained semantic equations and preservation obligations. Existing shared readers must continue to
reject unsupported versions correctly; an incompatible update cannot silently
reinterpret their accepted carriers. Full migration later closes the existing
source/artifact checking obligations, separately from foundation execution.

## Illustrative pseudocode

These sketches explain ownership and composition. They are not proposed parser
syntax, complete cryptographic algorithms or executable examples. Residual helper
names leave the carrier choice open. Helpers below
stand for inspectable definitions over admitted mathematics, not opaque protocol
primitives. `send` returns the receiver's actual supplied value.

```text
# Sumcheck: verifier state is computed from received coefficients.
stateP = residual_init(original)
pointP, pointV, claimV = [], [], supplied_claimV
repeat selected_rounds carry (stateP, pointP, pointV, claimV, coinsV):
    coeffsP = round_coefficients(stateP)
    coeffsV = send(P, V, coeffsP)
    V: guard degree_and_boundary(coeffsV, claimV)
    V: (rV, coinsV) = draw(coinsV)
    rP = send(V, P, rV)
    stateP = residual_bind(stateP, rP)
    pointP, pointV = append(pointP, rP), append(pointV, rV)
    claimV = evaluate(coeffsV, rV)
# Committed-original variant:
result = apply OriginalOpening(P.original, P.pointP,
                               V.commitment, V.pointV, V.claimV)
return result.acceptedV
# Public-table variant instead ends with:
# V: return evaluate_public_table(original_tableV, pointV) == claimV

# Interactive weighted fold shape: no rollback after sending a round.
repeat selected_rounds carry (aP, bP, gP, hP, blindP, coinsV, historyV):
    (LP, RP, blindP) = weighted_cross_terms(aP, bP, gP, hP, blindP)
    (LV, RV) = send(P, V, (LP, RP))
    V: (xV, coinsV) = draw(coinsV)
    V: if xV == 0: stop DegenerateChallenge
    xP = send(V, P, xV)
    P: checked_nonzero_or_stop(xP)
    (aP, bP, gP, hP) = weighted_fold(aP, bP, gP, hP, xP)
    V: historyV = append(historyV, (LV, RV, xV))

# Authored BP+ FS construction: a retry encloses the whole proof algorithm.
P: within_attempt_budget:
    transcriptP = init_from_public_context(commitmentsP, parametersP)
    bufferP = empty_proof_buffer()
    attemptP, coinsP = full_bpplus_attempt(witnessP, transcriptP, coinsP, bufferP)
    if attemptP is RetryableZeroChallenge:
        discard bufferP             # consumed randomness/work remain consumed
        retry_whole_attempt
    if attemptP is FatalFailure:
        stop
    proofP = attemptP.completed_proof  # terminal challenges/checks ran inside attempt
    leave_attempt_controller
proofV = send(P, V, encode(proofP))  # publication occurs after a complete attempt
V: accepted = full_bpplus_verification(commitmentsV, proofV, parametersV)

# Groth16: visible QAP/MSM algebra and one typed proof message.
P: h_data = qap_coset_numerator(relation, assignment, domain)
P: (r, s, coinsP) = draw_two(coinsP)
P: proof = groth16_equations(assignment, h_data, proving_key, r, s)
proofV = send(P, V, proof)
V: accepted = pairing_equation(verifying_key, public_inputsV, proofV)

# AIR argument: trace generation and constraint generation have declared boundaries.
P: roots, custody = commit_traces(actual_traces)
rootsV = send(P, V, roots)
# Authored challenge schedule, auxiliary traces, quotients and claims appear here.
apply ConstraintReduction(trace_relation, rootsV, actual_received_claims)
apply OpeningReduction(rootsV, actual_pointsV, actual_valuesV)
apply LowDegreeCheck(actual_codeword_rootsV, actual_queriesV)
V: return conjunction_of_actual_checks
```

The AIR sketch names stages to show composition. A future claim of complete AIR
execution requires authoring its omitted arithmetic and schedule. Foundation
component tests implement and check the computations in their own declared scope.
The BP+ prover/verifier challenge components remain distinct after a changed
message. A complete BP+ implementation must expand its helpers into inspectable
range, folding, transcript and terminal stages. Generic attempt tests must
preserve exhausted/fatal/retry outcomes; the controller is bounded. Already
published interactive messages cannot be rolled back.

## Completion tests and limits

A foundation release requires all of the following, together with the
[foundation evidence milestone](../assurance.md#6-implementation-correspondence-policy).
Native Lean differential evidence remains a later explicit obligation; actual
source-to-emitted checking is required here.

- The structural requirements have no unresolved representation, composition or
  realization gap inside the selected executable profile. Each maps to an owner,
  implementation, composed executable tests and explicit limits. Each general
  abstraction has contrasting uses; a domain primitive such as pairing retains
  its exact domain-specific contract.
- Adding a new program within that profile needs only authored IR and declared
  inputs/installations. Compiler dispatch, admission and runtime behavior depend
  on operations and contracts, not protocol names. Tests cross region, call,
  shape, role and resource boundaries rather than checking only isolated ops.
- Structured relation signatures retain actual aggregate parameters, statements
  and witnesses with their domains/shapes, purposes and acceptance mapping.
  R1CS and AIR clients discriminate schema binding from actual satisfaction.
- Required domain/provider/key combinations cross all executable boundaries:
  mathematical admission, lowering, physical installation, entry constructors,
  codecs and terminal checks. Remaining bulk-domain and setup-input restrictions are
  explicit; a required extension has a contrasting executable consumer. This
  requires neither every provider implementation nor a runtime plugin system.
- Required interactions of aggregates, resource roots and history effects have
  a documented decision and positive/refusal controls. Separate resource ports
  may be the chosen contract; a missing required composition stays open.
- Independent noninteractive execution passes for the selected constructed and
  authored clients. Verification uses authorized public context and only the
  proof as prover-supplied evidence, checks the final decision and proof
  exhaustion, and refuses stale context, malformed encodings and trailing bytes.
  The attempt host publishes only a proof selected by its completion predicate;
  failures retain consumed work. One-shot execution reports its return coordinate
  and may produce a prefix; only independent validation establishes acceptance.
- Observation inputs remain connected to their mathematical operands across
  relevant transformations. Focused controls distinguish reused/fresh draws,
  alias bindings, altered receives, early stops and later disclosures. These
  checks preserve analysis inputs; no affine analyzer result is required.
- Growing and shrinking loop state, nested applications, zero iterations/empty containers,
  captures and mismatched role configurations have discriminating checks.
  Verify stored IR, serialized bundle and schedule size independently of selected
  runtime length. Check repeated calculations/guards/services, nested occurrence
  paths, zero-trip message sites, and per-role count disagreement explicitly.
- Mutation controls cover actual incoming messages, reordered transcripts,
  wrong terminal points/subjects, bad domains/axes, stale keys/configurations,
  wrong array sizes, changed resource roots and failures during execution.
- Recompute source/candidate checks on the actual emitted artifacts, following
  the [preservation boundaries](preservation.md#the-emitted-artifact). Checks of
  adjacent transformations compose through their actual subjects; neither copied
  provenance nor same-constructor reconstruction supplies a missing edge. Region or
  type extensions update projection, lowering, serialization, C++/Rust admission
  and relevant installed consumers together. Structural checks retain their
  bounded claim; no native refinement theorem is inferred.
- Existing source functionality stays available during coexistence. Select routes
  explicitly; no hidden fallback to the old compiler. Delete replaced internal
  code with its last migrated consumer, without deleting still-needed checking
  paths.
- Document measured capacity for the composed tests and selected executable
  profile. Selected bulk computations need compact realization at those sizes;
  host-authorized capacity must cover their actual inputs and messages. Keep
  migration capacity comparisons separate: excluding an existing
  supported case leaves its migration row open, without claiming resource
  preservation from equal mathematical results.

The milestone does not require universal expressiveness, cryptographic security
proofs, production constant-time assurance, complete protocol-library migration,
external prover/verifier compatibility, all old frontend/checker migrations,
a production zkVM, or a performance win. It does require contracts that keep
these later questions answerable without recovering erased protocol meaning.

## Primary references

- [Bulletproofs+ paper](https://eprint.iacr.org/2020/735): range reduction and
  weighted inner-product structure.
- [Pinned Monero implementation](https://github.com/monero-project/monero/blob/4f92268d7c16741cfb41e5bbe2aa46cc260a9ea5/src/ringct/bulletproofs_plus.cc): concrete folding, retry and representation requirements.
- [Groth16](https://eprint.iacr.org/2016/260) and [snarkjs prover](https://github.com/iden3/snarkjs/blob/v0.7.5/src/groth16_prove.js): QAP, group arithmetic and randomness boundaries.
- [Proofs, Arguments, and Zero-Knowledge](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf): Sumcheck's round and terminal obligations.
- [Pinned OpenVM verifier](https://github.com/openvm-org/stark-backend/blob/362c7ad8c6b042b320471a137e3eadec7ec69a44/crates/stark-backend/src/verifier/mod.rs) and [WHIR verifier](https://github.com/openvm-org/stark-backend/blob/362c7ad8c6b042b320471a137e3eadec7ec69a44/crates/stark-backend/src/verifier/whir.rs): heterogeneous proof structure and composed reductions.
- [MLIR SCF](https://mlir.llvm.org/docs/Dialects/SCFDialect/), [Tensor](https://mlir.llvm.org/docs/Dialects/TensorOps/), [interfaces](https://mlir.llvm.org/docs/Interfaces/) and [effects/speculation](https://mlir.llvm.org/docs/Rationale/SideEffectsAndSpeculation/): reusable machinery and its semantic limits.

These sources motivate the design; they do not establish optimality or correctness
of an unimplemented zkc extension.
