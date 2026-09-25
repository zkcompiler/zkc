# Interaction composition and atomic sessions

This guide applies [interaction and endpoint admission](../spec/language/interaction.md),
[finite phase analysis](../spec/profiles/compiler/finite-phases.md#abstract-phase-policy)
and [admission through interpretation](../spec/core/interpretations.md#phase-admission).
[Core execution](../spec/core/execution.md) owns stopped-result sequencing.

## 1. Sequencing needs the phase at return

Suppose an action is permitted only in phase `unused` and advances to `used`.
Two one-action bodies both conform at `unused`, but their sequence does not:
the second body actually starts at `used`. The `blind_sequence_invalid`
control detects this loss of the actual return boundary.

`Returns` relates returned values and phases. Its stop case is vacuous because
no returning continuation runs; it does not establish completion. INT-03
quantifies over every typed reply, not just those an honest handler produces.

## 2. The composition laws

[INT-04](../spec/language/interaction.md#phase-safe-sequencing)
connects a prefix's returned-value/phase condition to the suffix's actual entry
premise. `Boundary.actual_return` connects that structural condition to the
final phase of the actual instrumented execution. A stopping call supplies
no reply edge for a suffix.

These phase laws complement [complete-result contracts](contracts.md).
Phase-safe sequencing alone does not establish residual resource, fact,
alias or failure-effect conditions.

## 3. Public repetition and call bounds

A value/phase invariant makes repeated execution compositional. A stop ends
the loop with its accumulated effects. The invariant can relate an explicit
accumulator index to the phase; there is no implicit index in common source
control. [PROG-07](../spec/language/programs.md#structural-call-bounds)
composes operation bounds and connects them to actual checked-plan calls.

The repetition theorem accepts every natural count. Source admission supplies
the separate fact that the chosen count and bound are public.

## 4. Tagged sessions and shared state

[INT-06](../spec/language/interaction.md#atomic-sessions) advances the selected
session's phase while allowing shared runtime resources. The shared-counter
control produces `[(false,0), (true,1)]` in one order and
`[(true,0), (false,1)]` in the other. Both schedules obey their local phase
rules; their ordered observations differ.

Consequently, different session tags are insufficient grounds for reordering
calls. A rewrite needs the actual state/observation relation and any applicable
joint probability law. Atomic interleaving does not supply fairness or a
concurrent-security result.

## 5. Obligations passed to source formation and compilation

[INT-07](../spec/profiles/compiler/finite-phases.md#abstract-phase-policy)
specifies the current sufficient phase analysis. Its operation law covers all
typed arguments and the entire interpreted body, even when one source
operation expands into several calls. [INT-08](../spec/core/interpretations.md#phase-admission)
transports phase laws through such an interpretation.

Execution preservation alone cannot supply the phase premises. A
value-dependent guard may require stronger analysis than the current finite
phase-set checker; [its design guide](../compiler/phase-admission.md) explains
that incompleteness.

## 6. Theory review and formal coverage

Returned-phase predicates apply compositional partial-correctness reasoning.
Unlike a total-correctness weakest precondition, a stopped body need not
establish a returned postcondition. Local endpoint projection is a
[separate, conservative step](../rationale/participant-generation.md).

[Boundary](../../formal/Zkc/Semantics/Boundary.lean) proves the common laws;
[composition controls](../../formal/Tests/Composition.lean) exercise the one-use
phase, bounded invariant and shared-state schedules. The
[correspondence map](../spec/correspondence/programs.md) records their
precise scope.
