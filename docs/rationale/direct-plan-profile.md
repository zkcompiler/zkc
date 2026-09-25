# The direct plan is a reference profile, not a required representation

The [direct plan](../spec/profiles/compiler/direct-plan.md#typed-plans) has the
same control as a [typed program](../spec/language/programs.md#typed-control)
and an evaluator of its own. A program denotes a body that a handler then
runs; a plan
[sequences complete results](../spec/profiles/compiler/direct-plan.md#evaluation)
directly.
[Direct lowering](../spec/profiles/compiler/direct-plan.md#direct-lowering)
proves the two equal for every interpretation, handler, environment and
initial state. The specification keeps the pair as one profile and
[permits other representations](../spec/conventions.md#conformance-claims)
whose semantic relation is established.

## Alternatives

**Delete the plan.** That removes an independently stated evaluator and the
exact candidate side of the
[source-relative check](../spec/profiles/compiler/direct-plan.md#checked-plans),
and the semantic judgment becomes no simpler for it.

**Require a plan of every compiler.** Control is then written twice, through a
representation that the judgment does not need. A compiler may share one
carrier between source and candidate, as the
[compact region profile](../spec/profiles/compiler/direct-plan.md#compact-region-profile)
does, use structured SSA, or choose a lower instruction language, when its
representation relation justifies the choice. An existing mechanization of
such a framework is not by itself a reason to adopt it.

## Reason

Two evaluators that are stated separately and proved equal give a small
reference correspondence, and the plan is the typed object that a raw
candidate decodes to. That value belongs to this profile. Requiring it of
every compiler would make one implementation choice durable, where the
specification leaves physical storage and scheduling representations open.

## Reopen when

A compiler design shows that maintaining the duplicate datatype costs more
than its independent evaluator and its checking boundary are worth.
