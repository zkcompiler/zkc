# A representation relates complete results, with values read in the final states

The [representation relation](../spec/realization/representations.md#related-complete-results)
compares two completed executions. It requires related residual states, equal
stop reasons or returned values that are related in the states the two
executions actually leave, and equal ordered projections of their events.
Stopped results keep their states and events. The relation says nothing about
an execution that does not complete.

## Alternatives

**Relate returned values by equality, or through a codec fixed on the input
states.** A native return can be a handle whose meaning exists only in the state
the call leaves: slot `0` represents `7` in the heap `[7]` and not in `[8]`. A
relation that ignores the final states cannot express allocation followed by a
read through the returned handle, and it accepts a target that returns stale
contents or rolls back the writes of a failed call. One that ignores events
accepts a target that omits them.

**Require equal heaps.** This forbids harmless changes of representation. A
private native heap need not equal the logical state; the state and value
relations carry the correspondence that a consumer selected.

**Make divergence part of every behaviour.** Leroy's account of compiler
correctness counts termination, divergence and errors as observable behaviour
and separates semantic preservation from the success of compilation
[1, §2.1–2.2]. Executions here are finite and complete, so a divergence case
would enter every protocol theorem without any source that produces it. It
would also not supply what is missing: a finite logical execution does not show
that a native callback terminates. A native realization instead states its
admitted initial states and a completion argument or an explicit progress
assumption, as the
[capacity and progress](../spec/realization/representations.md#capacity-and-progress)
rule requires.

## Reason

Reading values in the final states is what lets the relation compose. The
[sequencing rule](../spec/realization/representations.md#sequencing-represented-values)
hands the suffix the related values at the residual states, and
[transitive composition](../spec/realization/representations.md#transitive-composition)
keeps the middle execution's state and value as its witness, so a value taken
from an unrelated heap cannot connect two steps.

## Reopen when

A supported interface is asynchronous or may diverge, so that a claim about it
needs a trace or simulation relation beyond completed atomic calls.

## References

1. Xavier Leroy, "Formal verification of a realistic compiler,"
   *Communications of the ACM* 52(7), 2009, pp. 107–115, §2.1–2.2.
   [Author manuscript](https://xavierleroy.org/publi/compcert-CACM.pdf).
