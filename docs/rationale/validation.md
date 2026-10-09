# Validate the actual transformation result

The compiler retains its input and checks each actual transformed candidate
before publication. Runtime admission separately checks the supplied executable
artifact. The [preservation guide](../compiler/preservation.md) owns the compared
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

The independent Lean model has a
[sound rule-based candidate check](../../formal/design/compiler-connection.md#checking-in-the-current-formal-model).
Its theorem concerns the exact plan reconstructed by that rule and compared with
the candidate. Native checks are bounded implementation checks; they are not
proved instances merely because they follow the same method. The
[assurance policy](../assurance.md#6-native-correspondence-policy) keeps those
evidence levels explicit.

[Translation validation](https://xavierleroy.org/publi/validation-scheduling.pdf)
provides the methodological precedent. Its published proofs do not cover zkc's
operation meanings, resource policies or protocol guarantees.
