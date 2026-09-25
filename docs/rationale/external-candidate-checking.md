# The consumer checks the actual changed artifact

An optimized plan reaches execution only as an external candidate that a
separate consumer checks. The consumer keeps the original request
independently of the producer, resolves the transformation rule to its own
fixed meaning, and
[checks the actual candidate](../spec/verification/refinement.md#checking-the-actual-candidate)
against that retained source. The immutable object it admits is the object the
executor consumes. Direct lowering stays as the regression baseline, and its
[format](../spec/profiles/compiler/direct-plan.md#context-validity-and-accepted-metadata)
accepts only its exact direct lowering; a changed plan travels in an exact
format of its own, specified together with its first consumer. The
[lowering design](../compiler/design.md#4-lowering-and-final-evidence) lists
what the boundary binds. Transformation validity, phase admission and usability
are separate judgments about those shared operands.

The [candidate-checking rationale](candidate-checking.md) owns the choice of a
sound validator over a verified optimizer. Here the additional decision is how
the consumer retains the source and admitted object, and how separate judgments
remain bound to them through execution.

## Alternatives

**Run the optimizer behind a trusted in-process wrapper.** The consumer then
relies on the producer's own account of what was transformed, instead of a
check it performs on the request it retained. This is a development step. It is
not a delivered optimizing compiler.

**Admit changed plans under the direct format.** That format names one rule,
direct lowering, and one claim, equality for all inputs and handlers. A changed
plan is not the direct lowering of its source, so the direct checker rejects
it. Another rule is an explicit extension with its own meanings and checking
laws, not a relabelled direct artifact.

**Let an execution-refinement certificate also carry phase admission.**
Equality of complete runs under one handler says nothing about the other legal
replies. Let a call return a Boolean, and let the phase policy allow `tick`
only after `true`. A source that calls `tick` only on `true` conforms. A
candidate that always calls `tick` agrees with it under a handler that always
returns `true`, and violates the policy on the legal reply `false`. Both
programs are typed and finite. Source phase evidence therefore reaches a
changed target only through an
[admission transport law](../spec/verification/refinement.md#effects-and-admission-timing),
a stronger denotation theorem at the same interaction, or separate target
admission. Phase evidence is required whenever the requested endpoint policy
requires it; leaving the field out waives nothing. A child with no interaction
can have a trivial policy.

## Reason

A validator of the concrete result can be verified apart from the heuristic
that produced it, so the producer needs no trust. Rideau and Leroy establish
the method for register allocation [1]. Their proof covers none of the effect,
input or protocol contracts here; the consumer's resolved rule supplies those.

## Reopen when

The producer itself is proved correct for the selected semantics, so that
checking its output adds no assurance, or a required transformation has no rule
that a consumer can resolve and check within its capacity.

## References

1. Silvain Rideau and Xavier Leroy, "Validating Register Allocation and
   Spilling," *CC 2010*, pp. 224–243.
   [Author PDF](https://xavierleroy.org/publi/validation-regalloc.pdf).
