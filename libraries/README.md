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
```

These checks cover interactive and separate proof execution, compilation options,
false inputs and malformed proofs. The repository version policy applies to the
libraries; internal edits do not create compatibility modules or version bumps.
