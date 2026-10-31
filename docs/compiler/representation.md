# Compiler representation

Mathematical values retain their domain meaning through the
[pipeline](pipeline.md). Logical types, operation contracts and role
availability remain separate from installed storage and implementation choices. A new
representation must preserve its declared values, complete outcomes, residual
state and observations under the [realization laws](../spec/realization/representations.md).

## Logical structure

Resolved domains identify fields, extension bases, scalar actions and digest
suites. SSA operands carry actual tables, prefixes, relation inputs and messages.
A label or matching shape cannot establish their provenance. Structured regions
retain captures, carried state, ordered yields and failure paths. Attributes
hold immutable descriptors and selected contracts, not mutable execution state.

Total mathematics can be simplified under its laws. Ordered local calls retain
partiality, effects and resource transitions. A mathematical identity alone does
not authorize moving a failure, erasing a draw or reusing a consumed capability.
[Operation contracts](operation-contracts.md) and
[local control](control.md) define those distinctions.

Physical aggregates retain their complete ordered child layouts separately from
the logical schema. Sequences and dense containers have one element layout;
variants retain every payload position of every alternative. Inactive values
allocate no payload, but their layouts still affect identity and admissibility.
Logical static arguments never become physical types.

The canonical physical spelling is `logical@representation[child-layouts]`.
Brackets are omitted exactly for the canonical default children; flat types have
no brackets. For example,
`sequence<field:bls12-381.fr>@logical.sequence/0[blst/fr]` selects resident scalar
elements. Execution reads the stored complete layout. It does not infer a
container's layout from its active values or reconstruct default children.

## Checked physical decisions

One physical plan retains the original subject, including retained maps and
[logical computation units](../spec/ir/computation.md), until selection and checking finish.
Numerical transforms propose a complete scoped execution candidate without changing that
subject. The candidate records the actual numerical choices, including ordered
fallbacks; compile-time permission flags alone do not determine those choices.
Numerical recipe selection retains an actual standard SCF schedule. Its consumer
constructs scoped Func/CF and Exec, and an independent reader compares the actual
bounds, state, captures, primitive occurrences and completion behavior. The
mathematical reader separately checks that scoped payload against the original
mathematics; neither check obtains equations from the emitter. Root return
packaging remains uncharged, while an entered control body's completion remains
charged. Scope and Outcome plumbing are excluded from logical data coordinates.

Selection checks complete physical feasibility before retaining a candidate.
An unavailable implementation or direct conversion can advance the implicated
numerical occurrence to another admitted realization. Specialized contractions,
pointwise expressions, vector operations and ordered execution share this bounded
selection process. Explicit implementation choices remain fixed; an unrelated
malformed operation or correspondence mismatch remains a refusal. Attempts share
compile-time allowances, including discarded candidate construction.
Numerical preparation transfers its private candidate into recipe emission;
it does not take another whole-context snapshot merely to change ownership.
Correspondence still reads the unchanged original subject. Failed attempts
discard the private candidate and retain their charged work. Whole-context finite
and numerical comparisons belong to one independent validation owner outside the
retry loop. Construction rejected by physical feasibility need not reconstruct
another context solely for comparison. A retained numerical payload must pass
both source-to-finite and finite-to-selected checks, including dormant declarations.
The validation allowance is not recreated on retry.

Physical lowering separates three steps:

1. Retain the numerical candidate and propose binding implementations, physical
   ports and direct conversions for its actual operations. Keep explicit
   application choices fixed and record any selected storage releases.
2. Establish independent numerical correspondence with the original mathematical
   subject before retaining the private immutable payload. Validate physical
   decisions against installed Contracts and actual SSA uses in that payload,
   including release positions and lifetimes. Revalidating public physical
   choices does not repeat mathematical reconstruction of an unchanged private
   payload. Only physical validation constructs a checked plan.
3. Clone the retained candidate, apply the checked decisions, independently check
   the actual physical output and publish once. Materialization performs no
   numerical selection or catalog search.

Physical operation indices refer to the selected scoped candidate. They are not
indices into the original mathematical subject. The checked object privately retains
that candidate and owns the physical choices. Inspection returns a separate clone.
Module identity and complete source content guard validation and publication;
stale input refuses. This is an invocation-local guard, not a persisted
certificate or protection against concurrent mutation of IR.

Each mismatched operand gets its conversion immediately before its consumer, in
operand order. Declarations may be shared; dynamic instructions and results are
not silently shared or hoisted. Callable root ports use installed defaults unless an
exact input/output occurrence is selected in the physical-plan options. Captures,
branch yields and loop state retain checked physical equations, including the
zero-iteration path. Operation results retain their selected representation until
a use needs conversion. Incompatible participant and local signatures refuse.
Aggregate proposal solves structural layout equalities before choosing defaults.
Selected ports are fixed constraints; constructor leaf layouts are preferences
with any required change performed by an admitted reached direct conversion.
Competing leaf preferences use deterministic source order. Scalar control joins
retain a unanimous live-yield layout and otherwise select the default. Each
variant payload has its own layout variable, so constraining one alternative
does not fix its siblings. Inactive alternatives remain part of the final
independently checked type.
The candidate catalog supplies preferences for installed implementations and
direct adapters. It cannot create a conversion law or install a new contract.

Physical ports refer to semantic payload definitions and uses. An instruction's
returned payload can be a CFG block argument; its producer coordinate remains
that instruction. Scope, outcome, transfer and administrative counters are not
represented data ports. The borrowed port index carries actual SSA associations,
not an independently editable executable model. Both proposal and validation
read the current admitted subject.

Outlined control bodies forward captured representations unchanged. A conversion
needed by an instruction inside a body executes there, immediately before that
instruction in operand order. An untaken branch or zero-trip loop therefore does
not execute body-only conversions. Loop state has one consistent representation
including the zero-trip result; a required change at a yield executes in the
reached iteration. Match payloads use the selected variant child layout. Every
actual control edge constrains its closed body's callable signature. Explicit
function-port requests name callable roots or participants; compiler-owned
outlined bodies have signatures derived from those edges. An inactive payload
without a default layout remains provisional until its complete variant layout
is solved; all published ports must have admitted physical types.

Explicit value-layout requests identify a semantic result by its actual retained
function, qualified site and result index. Administrative CFG and scope
operations carrying the same site are not additional selection targets. The
independent reader applies this same coordinate contract to the actual subject.

Materialization constructs the selected scoped CFG and inserts only recorded
conversions and releases. Its independent reader checks the resulting payload
flow, bindings, origins, closed-body references and operation order. Source
helper returns were already substituted without a completion charge; publishing
an executable callable root introduces its native charged completion explicitly.
The [status page](../status.md) distinguishes this resolved execution path from
numerical requests whose realization migration remains in progress.

Automatic diagonal contraction selection is an explicit direct optimizer/planner
option: `zkc-participant-pipeline{linear-contractions=true}` or the physical
planner's `linearContractions` setting. Entry compilation and the composed
`compileRun`/`compileNativeProof` paths leave it disabled. Constant-time MSM and
explicit physical implementation selection remain available. The planner checks
every actual result use against the selected port and algebraic contract. Declaration/work limits apply before
publication. [Preservation](verification.md) checks the materialized operations,
conversions and operands separately from proposal validation.

Contraction discovery follows actual payload uses in each scoped execution
body. A producer and all consumers must remain in that same semantic body; views cannot cross a branch, become loop state or escape through a return.
Operations keep their original order, including checks between consumers.
Candidate discovery enumerates applicable installed implementations by identity;
policy can reorder or withhold them. Registration order grants no preference.
Adding implementations can change an automatically selected artifact, whose
recorded physical choices determine execution costs and limits.

## Scheduled lifetimes

Scoped Func/CF bodies and reached Exec instructions form the executable
schedule. Physical planning preserves their order and records optional binding
releases alongside implementations, ports and conversions. With storage release
enabled, the producer chooses the earliest legal point in each closed execution
body. The checker validates the recorded choices independently; it does not
repeat that heuristic and accepts safe delayed or omitted releases. The option
controls automatic proposals, not which legal schedules the checker accepts.
Materialization consumes those choices without discovering last uses, and the
output reader checks the actual release positions and operands.

Schedule coordinates distinguish operation results, block arguments and
conversion results. A conversion is an actual use: its input and output can
have different last uses. A release must follow the definition and every use
in the same semantic body. Returned or yielded bindings escape, and used affine
bindings have already transferred their permission. Existing releases remain
ordered instructions. Only discardable physical types permit new releases.

Releasing a binding does not establish unique ownership of its backing. The VM
retains allocations still referenced by other bindings, views, frames or returned
values. This schedule grants no writable-buffer access or scratch reservation.
Releases add no execution tick and do not refund cumulative work or allocation.
Released storage stays logically charged until its region exits, as specified
by [Local control accounting](../spec/ir/control.md#execution).
Loop transformations and native arithmetic require their own representation and
failure contracts; they are not implied by lifetime selection.

## Execution and evidence

The emitted `zkc.program/0` executes through the shared Runner. Logical data,
physical storage and runtime handles have distinct identities and lifetimes.
Native custody, value limits, conversion failures and instruction charges remain
part of the executable contract. Sufficient-capacity mathematical equality does
not imply equal exhaustion or allocation behavior at arbitrary runtime caps.

The current [formal semantics](../../lean/docs/spec/semantics.md) proves selected
open-process and observation laws. Native physical lowering remains a separate
implementation boundary; these laws do not establish its correctness.

### Resident providers

BLS12-381 scalar/vector and G1/G2 scalar/bulk values have explicit `blst/fr`,
`blst/g1` and `blst/g2` representations. The `blst/resident/` implementations
consume these physical ports directly. Adjacent calls can retain provider-owned
buffers. Canonical function ports and Contracts defaults remain Arkworks. The
Target candidate catalog gives the following installed implementations priority
for automatic physical selection:

| Domain | Operations | Preferred implementation prefix |
|---|---|---|
| `bls12-381.g2` | `curve.scale`, `curve.scale_each`, `curve.vector_scale` | `blst/resident/` |
| `bls12-381.fr` | `pairing.check` | `blst/resident/` |

These static preferences include representation conversion costs in their
evaluation. G1 scaling and ordinary field arithmetic keep their canonical
automatic choices. Empty or very small work can still cost more with conversions;
this policy is not a cost optimizer or a guarantee for every program. Exact
source selections and requested implementations take precedence. MSM remains an
explicit choice because its variable-time authority is independent of selection.

The explicit BN254 alternative is `halo2curves-axiom/resident/<contract>`.
Its positive operation inventory covers field/vector arithmetic, G1/G2 algebra,
MSM and `pairing.check`. Flat field/vector ports use
`halo2curves-axiom/bn254.fr`, and group/groups ports use
`halo2curves-axiom/bn254.g1` or `halo2curves-axiom/bn254.g2`. Exact implementation
selections use the ordinary physical planner, which inserts conversions at
canonical ports and can retain explicitly selected function ports. These
descriptors require explicit selection and add no automatic Target preference.
There are no Halo GT, PCS, FFT, matrix, field-array or fixed-vector routes.
The compiler driver does not yet expose a general source `--provider` option;
the installed provider menu is available to exact physical selection requests.

The catalog checks each suggestion against the installed signature and retains
the canonical fallback. The physical planner records and independently validates
the actual crossings. Missing adapters advance affected automatic choices
through the existing bounded retry. An optional whole-program capacity refusal
advances automatic choices together, including choices connected through inferred
container layouts; this coarse fallback does not search for a minimum repair.
Fixed choices and exhausted selection work remain exact refusals. Native executes
the emitted bindings without provider search or runtime retry.

`native/representation.convert` implements only explicitly installed direct
conversions. Its logical arguments contain the erased logical type; its physical
arguments contain the complete source and target types, in that order.
Mathematical identity alone grants no adapter.
Conversions remain reached operations and retain their failure and capacity
boundaries. There is no call-local fallback that silently converts every
arithmetic invocation.

The [kernel guide](../../crates/zkc-kernels/README.md#alternative-bls12-381-provider)
documents remaining normalization, workspace, timing and allocation costs.
Residency does not grant wire permission, constant-time behavior, or compatible
GT and PCS custody. Variable-time MSM requires trusted execution authorization.
