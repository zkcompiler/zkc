# Structured arithmetic and managed native execution

zkc uses qualified upstream arithmetic regions to select maintained native
implementations. Generated kernel execution remains deferred. The useful
boundary is a pure calculation with explicit inputs and outputs, beneath the
participant's ordered checks, resource policy and protocol observations.
[Field regions](../spec/realization/field-regions.md),
[quotient regions](../spec/realization/heir-arithmetic.md), and
[managed invocation](../spec/runtime/numerical.md) define the current contracts.

## Reuse transformations where their semantics apply

Tensor and Linalg retain iteration, broadcasting and scalar arithmetic without
choosing a machine representation for a nominal field. Upstream CSE supplies
sharing in admitted field regions; an independent reader compares the actual
result with the retained source before a native consumer uses it. HEIR's
Polynomial and ModArith regions similarly retain quotient operations across
transform placement. This removes the need for an owned NTT dialect or another
pointwise sharing planner.

An upstream transformation is useful only within an admitted profile. In
particular, a parallel pointwise iteration does not establish legality of a
reduction, an integer lift, a failure-sensitive traversal or a machine-width
conversion. The existing field, quotient, formal-polynomial and finite-domain
subjects continue to distinguish those meanings.

The [Transform dialect](https://mlir.llvm.org/docs/Dialects/Transform/) separates
scheduling from payload operations. Its handles and effects govern the schedule;
they do not prove that the resulting arithmetic computes the source expression.
The current production transformations use upstream APIs directly. A separate
schedule language and PDL pattern library would add another maintained surface
without eliminating a current decision owner. Transform and Vector are useful
for code-generation studies; they are not required dependencies of native
execution. Reconsider a shipped schedule when actual target-specific choices
justify it and the final payload has a corresponding reader.

## Kernel generation is a separate decision

Generated code can specialize constants and combine quotient operations with
fewer intermediate conversions. A compound short-preimage calculation is a
plausible kernel boundary: its coefficient inputs and result stay separate from
canonical admission and the centered-norm observation. It does not require
compiling the participant or moving protocol authority into native code.

The same argument does not justify replacing every field implementation. For a
KoalaBear pointwise expression, converting native coefficients to canonical
64-bit words and reducing each machine operation can cost more than the
maintained field implementation. Tiling and vectorizing that representation
cannot recover the field-specific arithmetic strategy by themselves. Binary,
extension and wide prime fields also need their own exact representation
conversions. The canonical-word prototype is therefore rejected as a general
production default; field kernel generation remains a separate representation
and cost-selection problem.

Memory is another part of the boundary. Upstream
[bufferization](https://mlir.llvm.org/docs/Bufferization/) can introduce temporary
allocations and copies. Caller-owned output alone does not account for those
allocations. A generated implementation needs a checked workspace contract,
initialized private output, immutable input aliases and publication only after
success. Moving every fixed temporary into explicit caller storage is useful
for a bounded prototype, but does not establish a general allocator or a public
ABI. Native resource charges describe managed payloads, not total process RSS.

The selected production direction is consequently managed native execution with
qualified structured selection. Quotient-kernel AOT remains a promising future
extension; production deployment is deferred pending a design for exact
representation, target features, calling convention, dependency identity,
workspace, code authority and any required leakage policy. A static development
caller establishes none of those deployment contracts automatically. Whole-
participant AOT has no demonstrated need at this boundary.

## Keep native alternatives distinct

Prepared [exact quotient matrices](../spec/domains/quotient-matrices.md) reuse a
public matrix's transforms and share each input transform across output rows.
Their checked CRT capacity also admits protocol rings that lack a suitable
scalar NTT. These are explicit local prepared values, with charged retained
storage and actual digit-bound validation.

Direct transforms in a supported protocol ring avoid CRT conversion; a tiny
product can favor schoolbook arithmetic. Preparation may dominate one call and
be amortized over repeated calls. Keeping these implementations has a present
semantic and cost purpose. Their selection must compare the complete consumer,
including preparation, conversion, scratch and output publication, rather than
only transform counts. Compiler and Host costs are separate measurement
boundaries. Neither native checks nor generated execution establish a Lean
correspondence theorem or constant-time behavior.
