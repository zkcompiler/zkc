# Validate the actual transformation result

The compiler retains its input and checks each actual transformed candidate
before publication. Runtime admission separately checks the supplied executable
artifact. The [preservation guide](../compiler/verification.md) owns the compared
objects, recognized transformations and remaining assumptions.

## Why separate search from checking

Optimization heuristics and upstream folds can change without changing the
meaning a result must preserve. Checking a result allows those producers to
evolve while keeping an independently stated comparison. Re-running the same
producer algorithm would reproduce its mistakes; shared type and operation
contracts do not require shared transformation algorithms.

Formation and copied provenance are insufficient. A same-typed replacement can
change a send operand, a guard or a receive while preserving all metadata. The
consumer therefore retains the original independently, checks actual operands
and control, and binds publication to the object checked. A digest can identify
bytes; it cannot establish that they implement a source program.

The cost is conservative refusal. A correct rewrite outside the checker's laws
or work limits can be unsupported. That refusal establishes neither an error in
the protocol nor permission to execute an unchecked replacement. Proving a
producer can be an alternative where a useful independent check is too costly;
the current native producers and validators have no such general proof.

## Keep the claims separate

Source correspondence, phase admission, execution capacity and security answer
different questions. Agreement under one provider does not imply legality for
all possible replies. A mathematical equality does not imply equal behavior at
the same native instruction limit. Each claim retains its own premises.

The independent Lean [proof-request checker](../../lean/docs/spec/verification.md)
reconstructs the requested program subject separately from an untrusted candidate
proof. Its claims concern the exact admitted scalar program and selected property.
Native transformation checks are not automatically proved instances of it.
The [assurance policy](../assurance.md#native-correspondence) keeps those evidence
levels explicit.

[Translation validation](https://xavierleroy.org/publi/validation-scheduling.pdf)
provides the methodological precedent. Its published proofs do not cover zkc's
operation meanings, resource policies or protocol guarantees.

## Solver checks and schedule authoring

[MLIR SMT](https://mlir.llvm.org/docs/Dialects/SMT/) provides a reusable typed
query vocabulary and SMT-LIB export. The optional
[arithmetic validation command](../../common/tests/README.md#offline-arithmetic-model-validation)
uses it to compare centered CRT reconstruction with independent integer
formulas. Direct bitvector queries check the overflow-free word threshold;
deliberately wrapping arithmetic and an overly wide reconstruction interval
must produce counterexamples that replay in ordinary integer arithmetic.

This is a development validation tool. Its formulas are independently authored,
not translated from the Rust kernel or an arbitrary compiler candidate. An
UNSAT result relies on the query, exporter and solver; there is no independently
checked proof certificate. SAT models are checked against input premises and
recomputed observations, but model replay does not establish completeness.
Timeout, unknown, errors, unexpected status and invalid models fail the check.
No solver result changes native admission or a Lean theorem.

A solver-backed compiler rewrite would require a precise translation of the
actual source and candidate, a policy for solver trust or proof checking, and
bounded failure behavior. The current structural readers remain the admission
mechanism. This narrower adoption gives a maintained consumer to the external
SMT dialect without adding a runtime or ordinary-build solver dependency.

[Transform](https://mlir.llvm.org/docs/Dialects/Transform/) separates schedule
authoring from the payload being transformed. It is appropriate for reusable
placement, tiling or vectorization schedules and target exploration. An actual
LLVM elementwise-fusion comparison produced identical payload IR using a
Transform script and the fixed registered-pass pipeline. The interpreter rejects
unknown passes and stale consumed handles, but an empty match can succeed as a
no-op; a required match needs an explicit cardinality check.

The admitted HEIR path currently has one fixed placement/cleanup sequence.
Keep that sequence in its owning implementation. Introducing a schedule language
now would duplicate orchestration without adding an admitted transformation.
Use Transform when multiple reusable schedules or target tuning create a real
consumer, retaining the independent candidate reader in either case. PDL may
factor genuinely shared matching logic then; it is not introduced merely to
rewrite existing C++ patterns into another syntax. Neither scheduling dialect
establishes semantic correctness of its payload transformations.
