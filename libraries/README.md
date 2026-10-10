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
| [`zkc::symbolic`](zkc/symbolic.zkc) | `Array`, `Polynomial`, pack/get/mle/from_coefficients/coefficients/evaluate/fix_prefix/sum_suffix/fix_table/add/multiply/constant | Total formal polynomial expressions |
| [`zkc::boolean`](zkc/boolean.zkc) | both/either/different/negate | Total Boolean formulas; eager operands |
| [`schnorr`](schnorr/lib.zkc) | `DLog<G>`, `Schnorr<G>` | Discrete-log relation and three-message group protocol |
| [`sumcheck`](sumcheck/lib.zkc) | `Sumcheck<F, Max>` | Bounded multilinear Sumcheck over a public evaluation table |
| [`expression_sumcheck`](sumcheck/expression.zkc) | `Sumcheck<F, Max, A: Ring>` | Sumcheck for a captured ring expression over public multilinear tables |
| [`fri`](fri/lib.zkc) | `LowDegree<C, LogSize, TerminalLog, Rounds, Queries>` | Binary FRI over a natural-order two-adic coset |
| [`air_polynomial`, `air_table`, `air_stark`](air/README.md) | Scope polynomials, Bundle opening equations and `TableArgument` | A nonhiding KoalaBear/Ext8 argument for one present table, composed with FRI |
| [`air_interaction`, `air_bundle`](air/README.md#whole-bundle-argument) | `Reduction<F>`, `LogUp<F>`, `GrandProduct<F>`, `ThreeTableArgument` | Three-table multiset arguments with phased auxiliary commitments and shared FRI |

### Mathematics

Import only the modules a client needs. Native `fn` wrappers retain ordered
execution and the kernels' possible stop behavior: vector split/fold requires a
positive even length, point access checks bounds, arithmetic checks lengths,
and matrix products check dimensions. `fold` applies a scalar affine formula
through native `map` after splitting; both Sumcheck libraries use this definition.
It fixes one Boolean coordinate of an evaluation table. FRI folding additionally
uses its coset points and keeps its separate domain-specific operation.
`has_length<F, N>` compares the dynamic
length with explicit static `N`; it does not resize or pad a vector.

`zkc::symbolic::Polynomial<F, N>` is a formal expression with `N` variables.
`zkc::polynomial::Polynomial<F>` is runtime univariate coefficient data. Use
qualified paths when both occur in one module. Formal MLEs use MSB-first Boolean
coordinates. `mle<F, N>` keeps `N` explicit because inferring it would invert
`pow2(N)`; ordinary field, array and result inference still applies. Coefficients
are increasing powers; formal coefficient extraction checks its degree premise.
`fix_prefix` substitutes leading coordinates; `sum_suffix` sums trailing Boolean
coordinates. `fix_table` performs the same prefix substitution on an MLE table.
Their static arguments name the remaining arity and the fixed/summed arity;
these choices stay explicit when their sum alone would not determine them.
Generic preconditions are completed from the intrinsic contracts and checked
at each call. These modules select no field, commitment or transcript.

Use `!`, `&&` and `||` to write Boolean expressions. The `zkc::boolean` helpers
remain ordinary functions: `both(a, check(b))` evaluates both arguments even
when `a` is false. In local `fn` code, `a && check(b)` skips the call when `a`
is false. See the [Boolean rules](../docs/spec/language/definitions.md#boolean-formulas)
for mathematical formulas and resource checks.

The [mathematics client](../examples/projects/mathematics/README.md) compares
formal evaluation and runtime folding. Group arithmetic already has ordinary
`+`, `-` and scaling as `point * scalar`; no duplicate group wrapper is needed. Asset-specific
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
terminal value through `ring.point` on the final `A::Inputs` factors. Both roles
fold through `zkc::vector::fold`, whose private scalar helper is applied by
checked [`map`](../docs/spec/language/definitions.md#checked-pointwise-maps):
each row of the halves becomes
`low + (high - low) * r`. This is vector arithmetic on the table, not a
substitution into the arena. The
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

### FRI

`LowDegree` takes a prover word, nonzero coset shifts at P and V, shared round and
query counts, and verifier randomness. Honest execution uses the same shift at
both roles; separate arguments allow callers to derive it locally. V checks
against its own shift. It requires a two-adic field of odd
characteristic, a row commitment scheme and bounded index sampling. For
`N = 2^LogSize` and `r = Rounds`, the tested degree bound is
`degree < 2^(TerminalLog + r)`. At least one fold and one query are required;
the final domain has at least twice the coefficient bound. Runtime counts must
match the static profile. The word must have exactly `N` entries.

Rows use natural domain order. A fold pairs the entries at `i` and `i + N/2`,
which represent `x` and `-x`. Each layer is committed with width one, so both
entries have independent authentication paths. All roots and final coefficients
precede all query draws; all query draws precede the openings. The final
coefficient vector may be empty (the zero polynomial), and its length must not
exceed `2^TerminalLog`.

The result contains the acceptance Boolean, query positions at both roles and
the authenticated first-layer values at V. A caller consumes these to check its
own polynomial-opening equations at exactly those positions. Successful return
means every verifier check passed; `accepted` is then `true`, and a stopped
verifier returns no result. The library does not attach a relation to an
arbitrary word. The [client](../examples/projects/fri/README.md) and independent
reference tests cover execution, compilation options, profiles, malformed
schedules, degree violations, mutated proof messages, dishonest prover folds
and terminals, and transcript event order. These tests establish no proximity
or Fiat–Shamir soundness theorem.

### AIR STARK

The [AIR modules](air/README.md) derive the constraints, scopes, opening subjects
and quotient bounds from a captured Bundle. They interpolate base-field trace
columns, construct extension-field quotient chunks, check out-of-domain claims,
and tie the original committed rows to the positions and values returned by FRI.
Vector combinations use checked native maps; protocol order stays in source.

The [recurrence project](../examples/projects/air-stark/README.md) consumes an
actual Plonky3 export through independent prover and verifier Hosts. Its small
parameters exercise a complete selected nonhiding profile. The
[accumulator-machine project](../examples/projects/accumulator-machine/README.md)
adds three-table composition, optional memory and interchangeable source LogUp
and grand-product reductions. The module guide states supported interactions,
shared degree bounds and sampling exhaustion. Security reductions for these
exact profiles remain separate obligations.

## Use a module

Imports resolve through explicit compiler module maps:

```text
use schnorr::{Schnorr};
```

```sh
zkc compile --module=schnorr=libraries/schnorr/lib.zkc \
  --module=example=examples/projects/schnorr/main.zkc \
  example::Proof --output=proof.zkpkg
```

See the [walkthrough](../docs/getting-started.md) to invoke the compiled Entry.
Project files can record these maps; see [project inputs](../docs/language/README.md#project-inputs).
Check the shared math modules with `zkc check --project=libraries/zkc/zkc.toml`.
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
uv run --no-sync --locked pytest tests/protocol/test_native_map.py
```

These checks cover interactive and separate proof execution, compilation options,
false inputs and malformed proofs. The repository version policy applies to the
libraries; internal edits do not create compatibility modules or version bumps.
