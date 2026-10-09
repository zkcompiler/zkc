# Sumcheck over a shared expression

This client computes the sum of `x * y` over a public table of factor values.
The ordinary [Sumcheck library](../../../libraries/sumcheck/expression.zkc)
receives a statically selected `Expression` component. That component binds
the [product arena](product.ring.json) through the captured name `product`.
The compiler derives its input width and round degree from the admitted
contents and retains those contents in the Entry package. The component uses
the same native evaluator available to AIR consumers.

`BaseRun` and `BaseProof` accept KoalaBear values and explicitly embed them in
Ext8 before the first round. `ExtensionRun` and `Proof` accept Ext8 values.
All four use Ext8 challenges. Each row contains the two factors consecutively;
folds eliminate the most significant Boolean variable first. A four-row table
`[1,2, 3,4, 5,6, 7,8]` has claim `100` and two rounds.

The prover sends the exact coefficients of each round polynomial. The verifier
uses the received vector, checks its length and its sum at zero and one, folds
its public factor tables and evaluates the terminal expression. Too few rounds
fail the terminal shape check; too many fail the next input-shape preflight.
The result is a public-table protocol with direct terminal evaluation, without
a polynomial commitment or a claimed soundness/Fiat–Shamir theorem.

Compile from the repository root:

```sh
zkc compile --entry=example::BaseProof \
  --module=example=examples/projects/expression-sumcheck/main.zkc \
  --module=expression_sumcheck=libraries/sumcheck/expression.zkc \
  --asset=product=ring-json=examples/projects/expression-sumcheck/product.ring.json \
  --output=expression.entry
```

Each independent Host admits the packaged expression before execution:

```sh
zkc prove expression.entry EXPECTED_SHA256 prover.json proof.bin
zkc verify expression.entry EXPECTED_SHA256 verifier.json proof.bin
```

Use named public inputs `values`, `claim`, and `rounds` in the ordinary
`zkc.entry-proof/0` request. The maintained
[integration tests](../../../tests/protocol/test_expression_sumcheck.py)
construct independent native wire encodings and cover both input fields,
simplification and storage-release modes, interactive execution, altered
coefficients, false claims, changed public inputs, asset substitution, and a
three-input cubic expression using the same source client.
See the [ring contract](../../../docs/spec/domains/ring-expressions.md) for
layouts, exact coefficient semantics, asset admission and work limits.
