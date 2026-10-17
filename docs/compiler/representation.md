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

Physical lowering separates three steps inside Target and Conversion:

1. Propose binding implementations, physical ports and direct conversions against
   unchanged logical IR. Keep explicit application choices fixed.
2. Independently validate the proposal against installed Contracts, actual SSA
   uses and the selected policy. Only validation constructs a checked plan.
3. Materialize that plan on an owned candidate, verify the resulting IR and
   publish it. Materialization does not search for another implementation.

The checked object owns choices and binds the current module identity and input
content. Stale input refuses. This is an invocation-local guard, not a persisted
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

## Execution and evidence

The emitted `zkc.program/0` executes through the shared Runner. Logical data,
physical storage and runtime handles have distinct identities and lifetimes.
Native custody, value limits, conversion failures and instruction charges remain
part of the executable contract. Sufficient-capacity mathematical equality does
not imply equal exhaustion or allocation behavior at arbitrary runtime caps.

The current [formal semantics](../../lean/docs/spec/semantics.md) proves selected
open-process and observation laws. Native physical lowering remains a separate
implementation boundary; these laws do not establish its correctness.
