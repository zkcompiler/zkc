# Ring expressions and the Clean adapter

`Zkc.Algebra.RingExpression` defines a finite arithmetic expression and evaluation.
`Zkc.Relation.AIR` adds noncyclic row offsets, scopes and checked windows. Out-of-
range reads are refused; last-row transitions do not wrap. Polynomial evaluation
and degree laws concern this mathematical model.

`Zkc.Relation.AIR.RingExpression` connects admitted AIR expressions to that ring
language. `ZkcClean` exports a lookup-free and channel-free flat Clean component,
proves constraint interpretation and source-specification preservation, and
emits the maintained finite native fixture. See the [adapter guide](../../integrations/clean/README.md).
The proof does not establish native decoder/provider correctness or a complete
AIR proof system's cryptographic soundness.
