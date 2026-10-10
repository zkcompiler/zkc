# Participant generation preserves explicit communication

The [native pipeline](../compiler/pipeline.md#preparation-and-projection)
derives participant programs from admitted common mathematics. Projection
preserves authored exchanges and refuses when a role lacks a needed value.

Inserting a message to repair availability changes what participants observe.
Having enough information to compute also differs from permission to reveal a
result. Additional communication therefore belongs in the authored protocol or
in a transformation with an explicit observation relation.

A receive is a fresh role-local input. Replacing it with an already available
same-typed value would assume honest delivery and could remove a check on hostile
input. The [role-indexed comparison](../compiler/verification.md#role-indexed-value-correspondence)
keeps actual receives distinct; honest transport is a separate premise.

Dynamic global choice needs its own projection rule. A participant must know
the branch, have equivalent continuations, or learn the choice through explicit
communication. Erasing a guard or inventing communication cannot supply that
rule. The independent [interaction model](../../lean/docs/spec/language/interaction.md)
and [shared-control reference](../../lean/docs/spec/profiles/source/located-execution.md#actual-agreement-for-shared-control)
state their own locality and agreement conditions.

This conservative policy can decline protocols with a valid implementation.
A broader projector needs concrete control, merge and observation laws and a
way for each affected participant to obtain its branch information.
