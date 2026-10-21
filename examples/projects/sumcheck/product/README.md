# Sumcheck over a shared expression

This client computes the sum of `x * y` over a public table of factor values.
It declares `domain Product = ring(asset product)` over the captured
[product arena](product.ring.json) and applies the generic
[Sumcheck library](../../../../libraries/protocols/polynomial/sumcheck/expression.zkc) as
`Sumcheck<Extension, 16, Product>`. The library derives the table width and
the round-polynomial degree from the arena; the compiler retains the admitted
contents in the Entry package. A different arena, such as a three-factor
product, changes the compiled rounds without editing the client or the library.
The kernels are the same native evaluator available to AIR consumers.

`BaseSumcheck` and `BaseProof` accept KoalaBear values and explicitly embed them in
Ext8 before the first round. `ExtensionSumcheck` and `Proof` accept Ext8 values.
The two concrete protocols provide their run Entries without wrappers.
All four use Ext8 challenges. Each row contains the two factors consecutively;
folds eliminate the most significant Boolean variable first. A four-row table
`[1,2, 3,4, 5,6, 7,8]` has claim `100` and two rounds.

The prover sends the exact coefficients of each round polynomial. The verifier
uses the received vector and checks its length and its sum at zero and one.
After the reduction, it folds its own public factor tables at the recorded
point and evaluates the terminal expression. The prover checks the table
against the full round count before sending a message. The verifier independently
checks its factor-table dimensions during terminal evaluation.
The result is a public-table protocol with direct terminal evaluation, without
a polynomial commitment or a claimed soundness/Fiat–Shamir theorem.

From this project directory, create `public.json`:

```json
{"values":["1","2","3","4","5","6","7","8"],"claim":"100","rounds":"2"}
```

Then run the base-field proof Entry explicitly:

```sh
zkc prove BaseProof --public=public.json --output=proof.bin
zkc verify BaseProof --public=public.json --proof=proof.bin
```

Each independent Host admits the packaged expression before execution. The
[integration tests](../../../../common/tests/protocol/test_expression_sumcheck.py) cover
both input fields, compiler policies, interactive execution, altered coefficients,
false claims, changed public inputs, asset substitution and a three-input cubic
expression using the same source client.
See the [ring contract](../../../../docs/spec/domains/ring-expressions.md) for
layouts, exact coefficient semantics, asset admission and work limits.

## Executable quick start

Run these literal commands from this project directory with `zkc` and
`zkc-compile` on `PATH` (Python 3 for generated inputs). The test suite runs
this block in a separate consumer tree using only declared package dependencies.

```sh zkc-example
mkdir -p build
printf '%s\n' '{"values":["1","2","3","4","5","6","7","8"],"claim":"100","rounds":"2"}' > build/public.json
zkc check
zkc prove BaseProof --public=build/public.json --output=build/product.proof
zkc verify BaseProof --public=build/public.json --proof=build/product.proof
```

Inputs: The recipe writes its public base-field factor table; product.ring.json is a captured expression.

Profile: BaseProof embeds KoalaBear into the octic extension; degree and width come from the captured expression.

Expected negative control: Changing the claim from 100 to 101 refuses acceptance.

Generated packages, proofs and result documents are written under `build/`
inside this project. Existing input maps remain source inputs.
