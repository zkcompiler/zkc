# Ring expressions and the Clean adapter

These models cover ring-expression evaluation and the flat Clean/AIR
connection; native decoder and provider correctness and the cryptographic
soundness of a complete AIR proof system are separate claims.

`Zkc.Algebra.RingExpression` defines a finite arithmetic expression and evaluation;
`Zkc.Algebra.RingExpression.Basic` holds the tree and its evaluation alone, which
the [executable stage](executable.md) uses to read the expressions of native
numerical calls.
`Zkc.Relation.AIR` adds noncyclic row offsets, scopes and checked windows. Out-of-
range reads are refused; last-row transitions do not wrap. Polynomial evaluation
and degree laws concern this mathematical model.

`Zkc.Relation.AIR.RingExpression` connects admitted AIR expressions to that ring
language. `ZkcClean` exports a lookup-free and channel-free flat Clean component,
proves constraint interpretation and source-specification preservation, and
emits the maintained finite native fixture. See the [adapter guide](../../integrations/clean/README.md).
