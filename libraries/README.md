# Libraries

Reusable `.zkc` modules are maintained with the compiler in this repository.
They define algorithms, relations and protocol interfaces. Applications select
concrete domains, Entries and transcript constructions in
[example projects](../examples/projects/README.md).

## Modules

| Module | Public exports | Contract |
|---|---|---|
| [`zkc::vector`](zkc/vector.zkc) | `Vector`, length/get/sum/split/add/scale/dot/fill/fold/has_length | Ordered finite vectors; fold pairs contiguous halves |
| [`zkc::matrix`](zkc/matrix.zkc) | `Matrix`, multiply/transpose_multiply/bilinear/rows/columns | Ordered sparse matrix operations |
| [`zkc::polynomial`](zkc/polynomial.zkc) | `Polynomial`, from_coefficients/evaluate/boundary | Runtime univariate polynomial data; boundary is p(0) + p(1) |
| [`zkc::symbolic`](zkc/symbolic.zkc) | `Array`, `Polynomial`, pack/get/mle/from_coefficients/coefficients/evaluate/add/multiply/constant | Total formal polynomial expressions |
| [`zkc::boolean`](zkc/boolean.zkc) | both/either/different/negate | Total Boolean formulas; eager operands |
| [`schnorr`](schnorr/lib.zkc) | `DLog<G>`, `Schnorr<G>` | Discrete-log relation and three-message group protocol |
| [`sumcheck`](sumcheck/lib.zkc) | `Sumcheck<F, Max>` | Bounded multilinear Sumcheck over a public evaluation table |
| [`expression_sumcheck`](sumcheck/expression.zkc) | `Sumcheck<F, Max, A: Ring>` | Sumcheck for a captured ring expression over public multilinear tables |

### Mathematics

Import only the modules a client needs. Native `fn` wrappers retain ordered
execution and the kernels' possible stop behavior: vector split/fold requires a
positive even length, point access checks bounds, arithmetic checks lengths,
and matrix products check dimensions. `has_length<F, N>` compares the dynamic
length with explicit static `N`; it does not resize or pad a vector.

`zkc::symbolic::Polynomial<F, N>` is a formal expression with `N` variables.
`zkc::polynomial::Polynomial<F>` is runtime univariate coefficient data. Use
qualified paths when both occur in one module. Formal MLEs use MSB-first Boolean
coordinates. `mle<F, N>` keeps `N` explicit because inferring it would invert
`pow2(N)`; ordinary field, array and result inference still applies. Coefficients
are increasing powers; formal coefficient extraction checks its degree premise.
Generic preconditions are completed from the intrinsic contracts and checked
at each call. These modules select no field, commitment or transcript.

The [mathematics client](../examples/projects/mathematics/README.md) compares
formal evaluation and runtime folding. Group arithmetic already has ordinary
`+`, `-` and scalar `*`; no duplicate group wrapper is needed. Asset-specific
ring operations and component-specific PCS operations stay in their owning
libraries, using explicit asset/component parameters and installed kernels.

### Schnorr

`Schnorr` takes a base and point at both roles, a scalar at P, and separate
random services for the nonce at P and challenge at V. V returns whether
`base * response == commitment + point * challenge`. `DLog` associates the
statement with its witness; the declaration does not insert a verifier check.

Honest execution requires both roles to agree on the base and point.
The group requires `Group`, `Share` and `Wire`; its scalar requires `Share` and
`Wire`. Correct use requires suitable group parameters and nonce/challenge
sampling. The example selects BLS12-381 G1. Tests of that execution do not
establish security of every group or transcript choice.

### Sumcheck

`Sumcheck` takes a table at both roles, a claim at V and a round count.
Honest execution requires both roles to agree on the table and count.
`Max` bounds the number of rounds. Each reached split requires a positive even
table length. Acceptance requires one final element, so a table of length
`2^n` needs exactly `n` rounds. Splits use contiguous halves; the first challenge
fixes the table's most significant coordinate.

V retains and folds its public table for the terminal check. This library does
not hide the polynomial or use a commitment. The field requires `Field`, `Share`
and `Wire` with the selected vector kernels installed. The example uses
BLS12-381 Fr. Vector folding and Boolean formulas use the shared modules; `sums` and
`terminal` are private protocol helpers.

### Expression Sumcheck

The expression-based `Sumcheck` takes separate prover and verifier tables, a verifier claim,
and a shared round count. It is generic over a captured ring expression
`A: Ring` and requires `1 <= A::Inputs` and exactly one output
(`1 <= A::Outputs, A::Outputs <= 1`); a client passes an asset domain such as
`domain Product = ring(asset product)`. Tables contain `A::Inputs` columns in
row-major order. Both roles must use the same table, column order, arena and
round count for honest execution. Each round pairs the first and second halves
of the rows, so the first challenge fixes the most significant Boolean coordinate.

P sends exactly the coefficients of `sum_i P(low_i + (high_i - low_i) X)`
through the installed `ring.affine_sum` kernel, padded to `A::Degree + 1`
where `A::Degree` is the arena's largest output degree with every input
weighted one; the vector preserves trailing zeros before transmission. V checks
that coefficient count and the round sum, folds its own table, and checks the
terminal value through `ring.point` on the final `A::Inputs` factors. The
compiler derives the width and the degree bound from the admitted arena; no
author-supplied dimension is involved. The exactness of the kernels and the
degree bound are mathematical premises of the installed evaluator, not source
theorems.

The [maintained client](../examples/projects/expression-sumcheck/README.md)
uses the shared [ring evaluator](../docs/spec/domains/ring-expressions.md)
over KoalaBear tables promoted to Ext8, or Ext8 tables directly. It exercises
interactive and Fiat-Shamir execution with extension-field challenges. The
verifier holds the tables, so this client supplies neither a commitment scheme
nor a security theorem for hidden tables.

## Use a module

Imports resolve through explicit compiler module maps:

```text
use schnorr::{Schnorr};
```

```sh
zkc compile --module=schnorr=libraries/schnorr/lib.zkc \
  --module=example=examples/projects/schnorr/main.zkc \
  --entry=example::Proof --output=proof.entry
```

See the [walkthrough](../docs/getting-started.md) to invoke the compiled Entry.
Project files can record these maps; see [project inputs](../docs/language/README.md#project-inputs).
Check the shared math modules with `zkc check --project=libraries/zkc/zkc.json`.
There is no separate registry or library installation step.

## Maintain a library

Keep public exports small and helpers private. Document input ownership,
required capabilities, mathematical assumptions and the acceptance result.
Concrete domain, transcript, setup and application choices belong in the client.
Extract shared modules when multiple clients need the same contract; compiler
intrinsics and backend kernels retain their own implementation owners.

Library changes include their runnable clients and positive and negative checks
through the common compiler and Host. With built tools, run:

```sh
uv run --no-sync --locked pytest tests/protocol/test_source_projects.py
uv run --no-sync --locked pytest tests/protocol/test_expression_sumcheck.py
```

These checks cover interactive and separate proof execution, compilation options,
false inputs and malformed proofs. The repository version policy applies to the
libraries; internal edits do not create compatibility modules or version bumps.
