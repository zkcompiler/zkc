# Lowering is interpretation, not a fixed ladder of intermediate languages

An operation of one signature receives its meaning from an
[interpretation](../spec/core/interpretations.md): a body over another
signature. Interpretations compose, so successive lowering is a composition of
meanings, and an intermediate signature need not be a compiler representation.
The compiler builds an inspectable structured form only where an analysis or a
transformation consumes it, as the
[representation levels](../architecture.md#2-shared-meaning-and-representation-levels)
and the [compilation architecture](../compiler/protocol-pipeline.md#1-representations-and-their-consumers)
describe. Interaction legality, participant views, construction choice,
analysis facts, observations, property experiments and trust premises are
judgments and choices applied to those forms. They are not further forms.

## Alternatives

**One intermediate language per concept, in a fixed order.** Several of the
concepts are not representations: a phase predicate is not a representation of
memory, and a probability law is not a lowering of an operation signature.
Ordering them as stages suggests implications that fail. Global phase legality
does not give a participant knowledge of another participant's choice. Equality
of an immutable preparation does not permit reuse of correlated setup. A
completed round does not establish its terminal relation. Distinct session
names do not imply independent state. A fixed order also imposes stages that
some computations never use: Boolean, group and correlation-based computations
have no polynomial stage. A construction choice, an analysis fact or a property
judgment needs its meaning bound and inspectable wherever a consumer depends on
it. It does not need a syntax tree of its own.

**An opaque callback with a matching signature.** A compatible reply type
establishes no law of the operation, and an arbitrary closure cannot be assumed
serializable. A behavior outside the
[execution envelope](../spec/conventions.md#execution-envelope) that is hidden
inside an atomic callback gives only the appearance of coverage.

**Interpretation alone, with no materialized form.** Changing an interpretation
runs the same retained source through another call vocabulary. It produces no
finite lower-level source for an analysis to read. A pass that must inspect an
expanded algorithm constructs the target form and proves its connection to the
source, as the
[Horner rewrite](../spec/verification/refinement.md#interpreted-operation-laws)
does.

**A semantic core for each protocol.** It would duplicate the execution and
relation laws that the protocols share.

## Reason

Composition and
[execution fusion](../spec/core/interpretations.md#execution-fusion) give
progressive lowering a semantic account that keeps residual state, ordered
events and a stop inside an expansion. A rewrite law proved for a class of
handlers
[carries over](../spec/core/interpretations.md#preservation-of-operation-laws)
when the composite handler belongs to that class. Retaining high-level
structure until its consumer has used it follows the MLIR rationale [2].
Treating event interpretations as composed translations follows Interaction
Trees [1], whose coinductive semantics is richer than this model's scope.

Fresh challenges and a transcript-derived construction are alternative
interpretations of one vocabulary, not automatically equivalent outputs.
[Exchanging them](../spec/core/interpretations.md#sequencing-and-changing-construction-order)
needs its own law, and the composition laws prove no security transformation.

## Reopen when

A concrete client exhibits one of these: a counterexample to a supported law;
two required behaviors that the abstraction cannot tell apart; an admitted
endpoint that needs information it cannot obtain; a promised transformation
whose necessary premise cannot be represented; an observer or intervention
outside the execution envelope. More available theories or more possible
protocols do not reopen the choice.

## References

1. Li-yao Xia et al., "Interaction Trees: Representing Recursive and Impure
   Programs in Coq," *PACMPL* 4(POPL), Article 51, 2020, §3.3.
   [Author PDF](https://www.cis.upenn.edu/~stevez/papers/XZHH%2B20.pdf).
2. LLVM project, [MLIR Rationale](https://mlir.llvm.org/docs/Rationale/Rationale/).
