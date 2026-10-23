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

## Checked physical decisions

One physical plan retains the original subject, including retained maps and
[logical Kernel units](../spec/ir/kernel.md), until selection and checking finish.
Kernel transforms propose a complete Local candidate without changing that
subject. The candidate records the actual numerical choices, including ordered
fallbacks; compile-time permission flags alone do not determine those choices.
Selection checks complete physical feasibility before retaining a candidate.
An unavailable implementation or direct conversion can advance the implicated
numerical occurrence to another admitted realization. Specialized contractions,
pointwise expressions, vector operations and ordered execution share this bounded
selection process. Explicit implementation choices remain fixed; an unrelated
malformed operation or correspondence mismatch remains a refusal. Attempts share
compile-time allowances, including discarded candidate construction.

Physical lowering separates three steps:

1. Retain the numerical candidate and propose binding implementations, physical
   ports and direct conversions for its actual operations. Keep explicit
   application choices fixed and record any selected storage releases.
2. Independently check numerical correspondence with the original mathematical subject,
   then validate physical decisions against installed Contracts and actual SSA
   uses in the candidate, including release positions and lifetimes. Only
   validation constructs a checked plan.
3. Clone the retained candidate, apply the checked decisions, independently check
   the actual physical output and publish once. Materialization performs no
   numerical selection or catalog search.

Physical operation indices refer to the selected Local candidate. They are not
indices into the original mathematical subject. The checked object privately retains
that candidate and owns the physical choices. Inspection returns a separate clone.
Module identity and complete source content guard validation and publication;
stale input refuses. This is an invocation-local guard, not a persisted
certificate or protection against concurrent mutation of IR.

Each mismatched operand gets its conversion immediately before its consumer, in
operand order. Declarations may be shared; dynamic instructions and results are
not silently shared or hoisted. Function/control ports use installed defaults;
operation results retain their chosen representation until a use needs conversion.
The candidate catalog supplies preferences for installed implementations and
direct adapters. It cannot create a conversion law or install a new contract.

Automatic diagonal contraction selection is an explicit direct optimizer/planner
option: `zkc-participant-pipeline{linear-contractions=true}` or the physical
planner's `linearContractions` setting. Entry compilation and the composed
`compileRun`/`compileNativeProof` paths leave it disabled. Constant-time MSM and
explicit physical implementation selection remain available. The planner checks
every actual result use against the selected port and algebraic contract. Declaration/work limits apply before
publication. [Preservation](verification.md) checks the materialized operations,
conversions and operands separately from proposal validation.

Contraction discovery visits ordered SSA blocks inside local control flow as
well as function bodies. A producer and all consumers must remain in the same
block; views cannot cross a branch, become loop state or escape through a return.
Operations keep their original order, including checks between consumers.
Candidate discovery enumerates applicable installed implementations by identity;
policy can reorder or withhold them. Registration order grants no preference.
Adding implementations can change an automatically selected artifact, whose
recorded physical choices determine execution costs and limits.

## Retained implementation ownership

The source-to-implementation edge has one internal owner, `ImplementationPlan`.
It retains the exact source identity and contents, numerical selection policy,
explicit implementation requests and the actual selected executable realization.
Physical proposals share that immutable owner and separately record bindings,
ports, conversions, contractions and storage releases. Inspection returns owned
copies; modifying an inspection copy cannot change a checked implementation.
The owner borrows the original module and owns the selected realization when
there is one. The original module and its MLIR context must remain live through
validation and materialization. Source identity and contents are freshness
guards, not a replacement for that lifetime requirement.

Validation first checks source freshness and independently compares the retained
numerical realization, then checks physical decisions against that same subject.
Materialization applies the checked decisions without selecting numerical recipes
again. The present realization is a Local/provider program. This boundary does
not define a foreign ABI or admit generated machine code. Synchronous calls use
the existing [managed numerical contract](../spec/runtime/numerical.md).

Numerical proposal and physical feasibility remain one selection transaction.
Separating their retained state does not create a second search or a separately
committed numerical choice: a physical refusal can still change the implicated
numerical realization within the shared work budget.

See [dialect ownership](../rationale/dialect-ownership.md) for why semantic
boundaries and physical representations do not need separate copies of every op.

## Scheduled lifetimes

Structured Local control and selected Plan operations form the executable
schedule. Physical planning preserves their order and records optional binding
releases alongside implementations, ports and conversions. With storage release
enabled, the producer chooses the earliest legal point in each isolated Local
block. The checker validates the recorded choices independently; it does not
repeat that heuristic and accepts safe delayed or omitted releases. The option
controls automatic proposals, not which legal schedules the checker accepts.
Materialization consumes those choices without discovering last uses, and the
output reader checks the actual release positions and operands.

Schedule coordinates distinguish operation results, block arguments and
conversion results. A conversion is an actual use: its input and output can
have different last uses. A release must follow the definition and every use
in the same block. Returned or yielded bindings escape, and used affine
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

## Numerical consumer boundaries

Every numerical consumer enters the retained implementation plan and the same
checked physical-selection transaction. The following subjects have distinct
roles; their similar containers do not make their meanings interchangeable.

| Consumer | Source meaning and implementation boundary | Current execution |
|---|---|---|
| Scalar field operations | Nominal field operations; reached division and decoding checks remain ordered | Installed field operations |
| Pointwise maps and admitted lane formulas | Upstream Func/Tensor/Linalg regions, scalar broadcasts and exact field arithmetic; independent final payload comparison | Managed vector recipes, with eager shape checks outside the region |
| Finite reductions and nested traversals | `finite` domains, bounds, witnesses, order and empty identities; pure lane subexpressions use the same field-region reader | Checked bulk recipes where admitted; ordered Local traversal elsewhere |
| Formal polynomials and multilinear evaluations | `poly` retains coefficient meaning, variable arity and quotient observations; MLE tables retain their Boolean-cube interpretation | Native formal products, evaluations and specialized coset/MLE kernels |
| Scalar quotient calculations | Formal `R(q,n)` source; HEIR Polynomial/ModArith placement is the default proposal inside the admitted full-NTT profile | Independently checked managed coefficient/transform operations; coefficient execution outside the profile or optimization capacity |
| Exact quotient matrices | Explicit prepared matrix carrier, signed digit bound and strict CRT capacity | Managed RNS provider with retained preparation and caller-owned workspace |
| Sparse matrices, curve contractions and provider leaves | Nominal domain, shape and current implementation contracts; these are not general dense tensor calculations | Existing checked implementations and managed invocation |
| Ring assets | Captured reusable expressions with independent identity, degree and formal-product consumers | Ring provider; sharing here is separate from field-map CSE |

The field-region boundary supports BLS12-381 Fr, BN254 Fr, Ristretto255 scalars,
KoalaBear, its quartic and octic extensions, GF(2^64), and its cubic extension.
Support for a field does not imply that every operation is defined for it:
for example, fixed field arrays retain their installed domain restriction, and
binary fields have no odd-characteristic halving or two-adic coset profile.
No integer representation is inferred from the scalar's name.

The required HEIR package belongs to the compiler's Transforms component.
LLVM-only components and IR discovery remain independent of that dependency.
Default CLI, Host and SDK builds use the same qualified source and patch pins;
there is no alternate compiler switch that bypasses arithmetic qualification.
See the [execution rationale](../rationale/numerical-execution.md) for the
separate generated-kernel decision and current native alternatives.

## Execution and evidence

The emitted `zkc.program/0` executes through the shared Runner. Logical data,
physical storage and runtime handles have distinct identities and lifetimes.
Native custody, value limits, conversion failures and instruction charges remain
part of the executable contract. Sufficient-capacity mathematical equality does
not imply equal exhaustion or allocation behavior at arbitrary runtime caps.

The current [formal semantics](../../lean/docs/spec/semantics.md) proves selected
open-process and observation laws. Native physical lowering remains a separate
implementation boundary; these laws do not establish its correctness.
