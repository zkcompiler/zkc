# Libraries

Reusable `.zkc` modules are maintained with the compiler in this repository.
They define algorithms, relations and protocol interfaces. Applications select
concrete domains, Entries and transcript constructions in
[example projects](../examples/projects/README.md).

## Modules

| Module | Public exports | Contract |
|---|---|---|
| [`schnorr`](schnorr/lib.zkc) | `DLog<G>`, `Schnorr<G>` | Discrete-log relation and three-message group protocol |
| [`sumcheck`](sumcheck/lib.zkc) | `Vector<F>`, `Sumcheck<F, Max>` | Bounded multilinear Sumcheck over a public evaluation table |
| [`expression_sumcheck`](sumcheck/expression.zkc) | `Expression<F>`, `Sumcheck<F, Max, Width, Degree, E>` | Sumcheck for an expression in public multilinear tables, using a statically selected evaluator |

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
BLS12-381 Fr. Local `sums`, `fold`, `both` and `terminal` helpers remain private.

### Expression Sumcheck

The expression-based `Sumcheck` takes separate prover and verifier tables, a verifier claim,
and a shared round count. Tables contain `Width` columns in row-major order.
Both roles must use the same table, column order, expression component and
round count for honest execution. Each round pairs the first and second halves
of the rows, so the first challenge fixes the most significant Boolean coordinate.

The `Expression` component supplies round-polynomial coefficients and terminal
evaluation. Its `round` method must return exactly the coefficients of
`sum_i P(low_i + (high_i - low_i) X)` as a vector padded to `Degree + 1`;
the vector preserves trailing zeros before transmission. `evaluate` must
interpret the same expression. V checks the coefficient count and round sum,
folds its own table, and checks the terminal value. These component laws and
the degree bound are mathematical premises; the frontend checks their types.
For the native ring component, `Width` must equal the arena's input count and
`Degree` its derived degree with every input assigned weight one.

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
