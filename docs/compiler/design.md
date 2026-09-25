# Compiler implementation design

The [protocol pipeline](protocol-pipeline.md) joins common source, construction,
independent participant algorithms and physical execution; this chapter supplies
the lower-level responsibilities inside that architecture. The
[transformation specification](../spec/verification/refinement.md) owns meaning; the
[compiler guide](README.md) explains it. The compiler is
a set of [C++ components](../../compiler/README.md#components): MLIR-free common
services, coordinated IR/translation/verification, and upper compiler workflows.
Graph algorithms, cost models, search, rewrites, planning and emission remain
in the native compiler rather than crossing a per-operation language boundary. Rust
submits complete jobs and consumes completed artifacts.
The [representation decision](representation.md) selects the native
implementation and tests mixed-level representation.
The [component instantiation decision](components.md)
refines reusable definitions, selected environments and runtime invocations.
The [logical-call discussion](calls.md) separates implemented structured calls
from an explicit-successor alternative and identifies their shared obligations. Sections below describe both implemented and proposed responsibilities. The
[status page](../status.md) and [protocol pipeline](protocol-pipeline.md) identify
the implemented subset; a design responsibility is not a claim of an installed pass.
The [table and storage instance](table-storage/README.md) supplies the first table operations, original-rank residuals, complete effects,
native ownership and reservation contracts. It has Lean source/plan clients;
the [finite native table path](table-execution.md) also implements a decoder,
MLIR registration and owned storage. Broader source/endpoint admission and the
production integration of these contracts remain work.

## 1. Representation and dialects

PIR meaning is not a sequence of dialect names. An interaction constrains an
endpoint; a structured source denotes that endpoint; an execution plan realizes
it. Several dialects can coexist while individual regions are lowered.

| Library / namespace | Owns | Initial operations |
|---|---|---|
| PIR / `pir` | Participants, explicit bindings, bounded control, ordered calls and complete outcomes | `endpoint`, `invoke`, `repeat`, `continue`, `return`, `stop`, atomic session boundary |
| Algebra / `algebra` | Mathematical field/group identities and total algebra | Constants, add/multiply, explicit natural embedding, contracted group kernels |
| Polynomial / `poly` | Domains, variable order, factors, views, reductions and materialization requests | Restriction, evaluation, fold, FFT and reduction descriptors |
| Plan / `plan` | Selected storage, kernels, codecs, providers and executable control | Typed slots, allocation, kernel invocation, preparation lookup, decode, branch, repeat, release |

This table groups intended responsibilities. It does not freeze four production
dialects or require one dialect per abstraction level. In particular, the finite
table prototype's `plan` operations and Formal's direct `Compiler.Plan` do not
complete the physical-plan/OIR design. The component/call and selective-lowering
decisions take precedence over illustrative operation names in this chapter.

Create libraries when their first operation is implemented, not empty dialects
for every anticipated protocol. Merkle compression can begin as a contracted
pure kernel. Transcript absorption is an ordered call even when its primitive
compression is pure. FFT/MSM/pairing kernels may stay contracted, while their
arguments, domains, batching and surrounding checks remain visible.

Reuse builtin functions, symbols, `arith`, `scf`, `tensor`, `memref` and `linalg`
where their supported types and semantics match the lowered region. A machine
integer operation is not automatically field arithmetic. HEIR's
[Polynomial](https://heir.dev/docs/dialects/polynomial/) and
[ModArith](https://heir.dev/docs/dialects/modarith/) dialects are concrete reuse
candidates for univariate/quotient-ring arithmetic and modular lowering. zkc's
factor views, variable order, partial evaluation and demand contracts require
their own interpretation. Assess compatible components at the field-materialization
step; no HEIR dependency or verified conversion is adopted by this design. The
`poly` namespace above denotes zkc's domain representation, not HEIR's `polynomial`.

Use SSACFG regions for executable bodies. A callable algorithm is isolated from
above, implements the function interface, and receives ordered public parameters,
runtime inputs, immutable captures and module bindings explicitly. The admitted
call graph is initially acyclic; repetition has an explicit public bound. General
CFG cycles and recursion require an additional supported bounded interpretation.
MLIR's structural verifier alone does not establish this condition.

Types distinguish mathematical naturals, fields, groups, digests and domain/view
handles. A field descriptor resolves its characteristic, representation-independent
interpretation and any extension/basis/scalar-action contracts; a suite also
distinguishes scalar and base fields. Dynamic dimensions are operands with
checked constraints. Do not encode every dataflow fact in a type, or use a field
element as a loop counter. Machine `index`, limbs and pointer layouts enter only
with range and representation obligations.

ODS defines signatures and generated scaffolding; C++ verifiers check dependent
relationships. Semantic IDs and capture bindings belong in retained typed
attributes/properties and operands. Source locations and optimizer hints cannot
carry an obligation that disappears on export. This follows MLIR's
[operation](https://mlir.llvm.org/docs/DefiningDialects/Operations/) and
[dialect conventions](https://mlir.llvm.org/docs/Tutorials/CreatingADialect/).

The first portable boundary is finite source data with a typed interpretation,
not arbitrary MLIR assembly. Its required constructor families are explicit
bindings, pure expressions, branch, public bounded repetition, contracted invoke,
return and stop. Source and direct Plan interpretations are developed together
before optimization. The first implementation uses the small owned typed
carrier and [finite source/plan format](source-plan.md). The
[interactive route](protocol-pipeline.md) separately retains common protocols,
projects participant programs and selects physical implementations.

For each compilation, fix the referenced semantic environment: operation
signatures and interpretations, field/domain parameters, module contracts and
source binding requirements, including dormant declared dependencies. The
checker resolves these references in its own supported, versioned environment;
an operation name or producer-supplied summary cannot install new semantics.
Backend implementation selection fills contract slots under the consumer's
policy. It cannot change their meaning. This closes a particular compilation,
while new interpreted operations can be added in later builds.

Implement the typed signature/contract extension boundary with the first source
carrier. Local binding, sequencing and control depend on that signature rather
than on a Sumcheck-specific operation enumeration or a single global field.
Domain references identify mathematical interpretation separately from native
storage. Exercise two distinct field domains in one typed source and a registered
operation extension without rewriting generic binding/control rules. Separate
well-typed uses must work and accidental domain mixing must fail. The
native baseline still needs only one backend. Unsupported meanings remain
unsupported; extensibility does not authorize an uninterpreted call.

## 2. Calls, stopping and ordering

Calls must preserve returned/stopped outcomes, state ordering and selected-instance
scope. [Logical calls](calls.md) compares a successor-based representation with
the current structured calls and implicit stop propagation. The following is an
alternative CFG sketch, not a registered operation or supported parser form:

```text
pir.invoke @write(%flow, %cell, %value)
  returned ^reply(!pir.flow, !pir.reply<WriteError,Value>)
  stopped  ^exit(!pir.flow, !pir.stop)

^reply(%after, %reply):
  // A returned error can recover from the actual post-write state.
  ...
^exit(%after, %why):
  pir.stop %after, %why
```

The operation produces successor arguments on both edges. Its post-flow orders
the actual completed call, including failed writes and emissions. A Boolean
reply stays Boolean; the dialect does not invent recoverable exceptions for it.
The hidden world is interpreted by a handler, not exposed as an SSA record that
the participant can inspect. Branch interfaces describe successor dataflow;
they do not prove the handler contract.
[MLIR interfaces](https://mlir.llvm.org/docs/Interfaces/).

`pir.repeat` carries the natural iteration count, accumulators and flow. A body
returns updated accumulators or a local stopped outcome. A stopped body exits the
loop with its last state and event prefix and skips later iterations. Lower to an
explicit counter/exit CFG; use `scf.for` directly only for total, non-stopping
bodies after index correspondence. Atomic session bodies expose only the
controller intervention points admitted by their contract.

The path-sensitive verifier must reject obsolete-flow reuse, a same-path fork,
implicit flow capture and an exit carrying an old flow. Forwarding one flow to
mutually exclusive successors is legal. Counting SSA uses is insufficient.
For bounded loops, verify the entry/backedge/exit invariant structurally rather
than unroll all public iterations.

Use a zkc type for this ordering value. MLIR's builtin `token` has a different
contract: it cannot be forwarded through branch successors or loop-carried
arguments/results. It is not a replacement for `!pir.flow`. The distinction was
checked against the official [token documentation](https://mlir.llvm.org/docs/Tokens/)
and the installed LLVM 23 type constraints. Neither type supplies zkc's
path-sensitive usage law automatically.

Also give ordered calls conservative memory effects on a shared execution-order
resource and mark them non-speculatable. Tokens do not prevent all generic
rewrites, and MLIR does not supply linear typing. Finer resource footprints serve
zkc analysis initially; dropping the shared order requires a commuting-operation
law for the selected observer. An operation that can fail, consume input, draw
randomness or observably allocate is not `Pure` merely because it writes no
ordinary heap memory. Upstream distinguishes effects and speculation, and its
generic non-local-control model remains incomplete.
[Side effects and speculation](https://mlir.llvm.org/docs/Rationale/SideEffectsAndSpeculation/).

## 3. Analysis and optimization interfaces

The [size policy](../rationale/bounded-representation-cost.md)
selects conservative outcome merging with one continuation by default. The
[conservative rule](../spec/profiles/compiler/factor-preparation.md#conservative-typed-factor-rule)
now has its own complete-execution and structural-size proofs in Lean. The
native pass must realize that rule under its actual module and storage laws;
this does not yet bound descriptors, certificate bytes or checker work. The
original factor reference still specializes unequal outcomes. Optional
specialization has a global growth/work budget
covering production, checking and serialization. When the budget is exhausted
the compiler uses a checked direct alternative or the proved conservative
merge. If neither fits the consumer's capacity it reports a compiler or checker
capacity refusal before execution; it does not start the protocol and produce a
logical `exhausted` stop. Preserve source branches and
original-position guards when analysis facts are forgotten.

| Interface | Finite information produced | Semantic obligation |
|---|---|---|
| Semantic export | Constructor, schema, ordered operands, bindings and contract instance | Export denotes the selected source or plan |
| Module effects | Preconditions and outcome-specific writes, facts, availability and observations | Summary holds of the actual transition, including failure |
| Demand | Required factor/view prefixes, domains and origins | Demand suffices for the actual requested computation |
| Preparation | Immutable dependencies, exact key and direct/reuse alternatives | Equal complete keys denote equal prepared values; logical occurrences remain |
| Cost | Arithmetic/kernel work, bytes, memory and lookup/insertion costs | A separate prediction/measurement, never proof of semantic validity |

Implement semantic export and outcome-specific effect summaries with the first
registered calls. Add demand/preparation methods with their actual shared pass,
before protocol-specific rewrites can depend on ad hoc operation-name tests.
The pure and stateful clients must exercise the same extension path. Missing
summaries conservatively disable affected optimizations while an unknown
interpretation still prevents admitted export. Keep these semantic interfaces
independent of a particular C++ pattern, PDLL script or search representation.

Use separate forward facts/readiness, may-phase covers and backward demand
analyses, coordinating them where an actual transfer needs shared precision.
Must-facts intersect at joins; may-phases union; demands retain the requirements
of every remaining consumer. Solve coupled finite constraints to a post-fixpoint
only for analyses that actually need coupling. Unknown summaries
invalidate affected facts or prevent a proposed reuse. An unknown *meaning*
prevents certified export. Check loop invariants rather than assuming the worklist
algorithm or its termination proves semantic soundness. Finite invariant evidence
is independently checked against interpreted transfers. Abstract interpretation
supplies this division between a sound domain/transfer and a heuristic producer;
[translation validation](https://xavierleroy.org/publi/validation-regalloc.pdf)
supplies the concrete-result checking pattern.

Search over immutable candidate snapshots in C++. Bound search effort, preserve
a valid fallback, and retain a Pareto frontier where runtime work, memory and
wire size differ. Equality saturation is optional inside pure typed algebraic
regions; equations do not justify moving challenges or failure checks. Rebuild
the affected endpoint's analyses after each accepted rewrite initially. MLIR
analysis invalidation, semantic fact invalidation after a runtime call, and
cross-build evidence-cache invalidation are three separate mechanisms.
[Pass management](https://mlir.llvm.org/docs/PassManagement/).

A preparation key binds the immutable provider meaning and algorithm interpretation,
ordered immutable inputs, field/domain/suite and all actual dependencies. It
need not contain a unique invocation or full source identity when a law shows
those are irrelevant to the prepared value. Code sharing, preparation equality
and evidence reuse have different dependency sets. A hash
can index keys; compare the full key unless a collision assumption is part of the
claim. A changed mutable world may invalidate a live fact while leaving a table
prepared from frozen captures valid. Sharing sampled masks or skipping a tape
coordinate is not ordinary immutable memoization.

The current native table operations can refuse; the contextual preparation
study's provider is total. Their first production adapter keeps shape/readiness
guards at each logical occurrence and extracts only the total immutable work
on validated inputs. Physical allocation uses the selected capacity contract.
Prove the adapter against the actual table evaluator and complete stopped state
before applying the common preparation rule. The existing factor-guard law is
supporting evidence, not that missing native/table instance. Dominated reuse of
an already successful deterministic partial operation can be a later checked
rule; conservative flow/effects need not allow it initially.


## 4. Lowering and final evidence

The [target design](targets.md) selects two branches from retained logical
meaning: a closed physical execution plan and a verifier acceptance relation.
This section owns their common MLIR conversion and checking mechanisms.

The [admission boundary](../rationale/external-candidate-checking.md)
requires a separately checked external optimized artifact for the first useful
optimizing delivery. Version-1 direct lowering remains the baseline. Specify a
new exact format together with its consumer, beginning with one fixed Horner
rule before connecting the shared factor pass. Bind the actual source, final
candidate, meanings, relation, initial premises and any required phase evidence.
Phase evidence is required whenever the requested endpoint policy requires it;
omitting the field does not waive the policy. A child with no interaction can
have a trivial phase policy.
Source phase evidence reaches an optimized target only through its applicable
all-reply admission transport law or separate target admission, not from a
generic execution-refinement result alone.

| Boundary | Work | Required retained meaning |
|---|---|---|
| Admission to structured PIR | Decode source; bind roles, inputs, captures and public instance | Original admission domain, including dormant dependencies |
| PIR/domain optimization | Demand, preparation, algebraic and algorithmic choices | Ordered calls, failure paths, guards, factor/domain identities |
| Materialization to Plan | Buffer layouts, coarse kernels, cache operations, codecs and storage schedule | Heterogeneous values/states, aliases, residual errors and resource behavior |
| Plan export | Full conversion, finite typed serialization | Exact final plan, source, configuration, observer, contracts and requirements |
| Optional generated code | Lower kernels through appropriate MLIR backends or emit Rust in C++ | A separate downstream correspondence to the actual generated code/build |

Each conversion uses a `ConversionTarget` and interpreted rules; add a
`TypeConverter` when types change. The [selective-lowering study](lowering.md)
tests same-type expansion, actual-candidate comparison and evidence invalidation.
Mixed IR may use partial conversion; final export rejects unknown operations and
unresolved conversion casts. Recursive legality must not hide unsupported nested
operations. Generic canonicalization, CSE and bufferization also change meaning:
either cover them with registered rules or validate the resulting complete change.
A rewrite listener is provenance, not a proof.
[Dialect conversion](https://mlir.llvm.org/docs/DialectConversion/).

Flow is a compiler ordering value, not a serialized copy of cryptographic state.
It can disappear when the selected Plan control/dispatch order and its checked
interpretation carry the same causal constraint, including stops. Its erasure is
an explicit lowering obligation; a runtime token allocation is not required.

Do not apply whole-function bufferization before value, alias and failure
contracts exist. Allocation hoisting can change exhaustion and observable timing;
disjoint buffers do not establish provider independence. Required capacity can be
an admitted public precondition or a specified dynamic failure. Machine arithmetic
for sizes is checked. Field inversion by zero has its explicit mathematical/error
convention, never LLVM undefined behavior.
[Bufferization](https://mlir.llvm.org/docs/Bufferization/).

The driver retains source and requested policy independently of the compiler.
The candidate contains the final plan, constructor/contract versions, ordered
bindings, rule applications, invariants and explicit requirements. Each rule is
classified as execution refinement, representation refinement or protocol/property
transport. The checker resolves a rule to its own fixed semantics; it does not
execute arbitrary producer-supplied Lean code or trust a theorem-name string.

The first local optimization policy preserves returned values, exact logical
stops, related residual states and the consumer-selected ordered observation;
lowering uses the corresponding heterogeneous representation relation. Cost
accounting is separate. A candidate cannot weaken the observer or turn a
possibly failing source guard into an assumed successful precondition.
Requirements must have a permitted producer: checked evidence, a source-aligned
runtime guard, or an assumption explicitly allowed by the consumer. Candidate
capacity requirements are limited to the native progress policy described in
the [runtime design](../runtime/design.md#4-randomness-cancellation-and-resource-failure).
A conditional theorem alone does not admit execution under arbitrary premises.

Intended checker law, schematically:

```text
check(original, finalPlan, policy, evidence) = accepted(requirements)
  -> for every admitted runtime binding satisfying requirements,
     the requested relation holds between those exact interpretations
```

Kernel proof replay, a native checker result and a trusted backend registration
remain distinguishable evidence. The plan loaded by the runtime is the same
admitted object. Post-check optimization requires its own connection. Longer
compile budgets can buy stronger invariants, search and proof replay; they do not
buy permission to weaken a relation.

## 5. Validation workloads

The finite table route supplies an unoptimized regression reference: source
decoding, MLIR import/export, direct Plan lowering, source-relative checking and
Rust execution. Its representation connection is required even without
optimization. Pure arithmetic round trips alone do not exercise stateful failure.
The interactive participant route has separate source and artifact consumers.

Two polynomial workloads remain distinct. The dense reference has `3^n`
coefficients, so complete protocol comparison against it is limited to small
dimensions. Larger native table restriction and evaluation measurements do not
establish complete large-dimension Sumcheck support. The security companion uses
[direct evaluation of the original polynomial](../rationale/sumcheck-direct-terminal.md)
under a [named claim scope](../rationale/claim-scope.md).

Broader shared preparation work must join demand, outcome-sensitive fact framing
and immutable preparation on an actual field-valued factor client. Ordered
Merkle compression is a contrasting consumer: preparation reuse must retain
all path reads and checks. A Sumcheck Horner rule is a separate algebraic
checker client, and the natural-number factor proof does not automatically
supply the field-valued implementation connection.

Required controls distinguish failed-write recovery, terminal stop, revoked
readiness, swapped captures, differing full preparation keys, duplicated or stale
flow, characteristic-two fields with three natural iterations, changed final
plans and missing premises. Certificates should scale with structured bodies
and invariants rather than runtime round count. KZG aggregation and correlated
services distinguish transformations requiring a different property law.
[Status](../status.md) reports delivered checks; the [roadmap](../roadmap.md)
orders the remaining work.
