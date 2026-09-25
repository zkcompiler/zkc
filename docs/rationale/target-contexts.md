# A preserved property is claimed for a stated observer, not against arbitrary target code

A property [transports](../spec/properties/experiments.md#construction-changes-and-contexts)
through compilation only for the experiment and observer that the established
relation covers. The context that the common laws admit is a common
reply-adaptive body whose handlers are replaced under a stated relation. A
claim selects its actual observer and includes every artifact released to it,
the effects on provider state and any runtime channel it was promised. No claim
quantifies over arbitrary code linked against the compiled target.

## Alternatives

**Require full abstraction, or robust preservation against every target
context.** These criteria quantify over target contexts. They need a context
model that fixes linking, code inspection, intervention points, provider access
and the final observation, and an argument for every member of that class. No
such class is defined for the native target, so the criterion would be a claim
whose quantifier has no domain.

**Promote handler equality or a local algebraic law to a security theorem.** A
common reply-adaptive continuation is a narrower quantifier than arbitrary
target code. Abate et al. make the quantification over contexts explicit and
separate the preservation of properties of single programs from that of
relations between several runs [1, §3.1, §4.4]. Their separating example uses
a context that inspects code. It applies directly to an artifact generated from
a secret: equal runtime behaviour does not hide generated code that the
recipient can read.

## Reason

Stating the observer keeps the scope implementable and prevents a local law
from being read as a stronger theorem. A
[representation relation](../spec/realization/representations.md#observers)
justifies the suffixes and observers determined by it, and no others; equal
events give no law for memory, timing or allocation. Whether specialization
reveals information through its code is a separate
[release obligation](../spec/realization/artifacts.md#specialization-and-retained-configuration)
even where execution refinement holds.

## Reopen when

A class of target contexts is defined for a supported native target, stating
what such code may link against, inspect and call, or a consumer asks for a
relational property against code the claim does not control.

## References

1. Carmine Abate, Roberto Blanco, Deepak Garg, Cătălin Hriţcu, Marco Patrignani
   and Jérémy Thibault, "Journey Beyond Full Abstraction: Exploring Robust
   Property Preservation for Secure Compilation," *CSF* 2019, pp. 256–271,
   §3.1 and §4.4. [Extended version](https://arxiv.org/pdf/1807.04603).
