# Semantic model choices

These choices concern the independent Lean models. The
[execution specification](../../docs/spec/core/execution.md) owns their meaning;
the [native mathematical IR](../../docs/rationale/mathematical-ir.md) has its own
representations and still needs an explicit formal correspondence.

## Bodies and operations

A body is a well-founded tree of return, stop and operation requests whose
continuations receive actual replies. Handlers supply state, randomness and
services. This retains the structure needed for all-reply conformance and public
call bounds. An opaque monadic action would hide those calls. Taking compiler
operations themselves as meaning would instead tie the model to one carrier.

The tree is a denotation. Portable source uses finite typed syntax, and compiler
representations can share regions and keep loops compactly; no continuation
serialization or tree allocation follows from the semantics.

Typed source has common control and parameterized sorts and operations. Field,
group and Merkle clients can reuse binding, renaming, sequencing and structural
call bounds. A universal operation enumeration would make every domain extension
change common control; a universal polynomial object would not describe every
domain. An interpreted operation retains more useful structure than an opaque
whole verifier. Portable profiles still need finite descriptors and checked raw
formation: a mathematical operation parameter alone supplies no codec.

An operation signature carries no algebraic equations. A rewrite requires a law
of its selected interpretation. This follows the distinction between operations
and handlers in [Plotkin and Pretnar](https://arxiv.org/pdf/1312.1399); a matching
reply type does not justify a replacement.

## Interpretation and representations

An [interpretation](../../docs/spec/core/interpretations.md) expands one operation
into a body over another signature. Composition and execution fusion account for
state, ordered events and stops inside that expansion. A rewrite transports only
when the resulting handler satisfies its law.

An intermediate signature need not be an intermediate compiler representation.
Phase legality, analysis facts and probability laws are different judgments,
not successive syntaxes. Conversely, interpretation alone does not construct
finite target syntax for an analysis to inspect. A materialized expansion needs
its own relation to the source. No separate semantic core is needed per protocol.

Fresh random challenges and transcript-derived challenges can interpret the same
vocabulary, but need not yield equivalent runs. Changing their construction or
order needs its own law; interpretation composition proves no Fiat–Shamir
security transformation. Distinct session names likewise do not imply independent
state, and global legality does not imply participant knowledge.

## Finite bodies and outer iteration

[Outer iteration](../../docs/spec/core/iteration.md) repeats finite bodies and
retains coherent pending prefixes. The unbounded reference has no finite endpoint
bound. A deployment cap can explicitly turn pending work into exhaustion; proof
fuel cannot silently become an operational stop. Failed attempts retain actual
state and events.

This reuses induction and finite sequencing laws. Replacing every body with a
coinductive calculus would add divergence and bisimulation obligations to passes
that consume finite bodies. Hiding a whole loop in a provider would instead lose
inspectable work. Recursive stored bodies, fairness, infinite interactive traces
or interruption within an atomic step can warrant a richer model when finite
segmentation cannot preserve the required observations.

[Interaction Trees](https://arxiv.org/pdf/1906.00046) and
[Capretta's partial computations](https://lmcs.episciences.org/2265) give broader
recursive models. They inform this distinction without supplying proofs of zkc's
model.

## Direct plans

The [direct-plan profile](../../docs/spec/profiles/compiler/direct-plan.md) keeps
an independently stated evaluator and proves it equal to source denotation for
all its interpretations, handlers, environments and initial states. It also
provides an exact decoded candidate for the source-relative checker.

Deleting that datatype would remove a useful independent evaluator; requiring it
of every compiler would duplicate control without a semantic need. Other
representations, including shared source/candidate carriers and structured SSA,
can satisfy their own relation. The direct plan is a formal reference profile,
not another mandatory stage in the native compiler.
