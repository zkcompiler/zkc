# Binary FRI

This client runs the reusable [`fri::ScalarLowDegree`](../../../libraries/protocols/polynomial/fri/lib.zkc)
protocol over the KoalaBear degree-eight extension field and logical table
oracles. A deployment selects ideal data or an installed Merkle realization. It tests a word of 32 evaluations on a nonzero two-adic coset for a
polynomial of degree below 8, using three folds and eight queries. These small
parameters exercise the implementation; they are not a security recommendation.

The prover sends each logical word before receiving its folding challenge. After the
last fold it sends coefficients of a constant polynomial. The verifier checks
the degree bound, draws all query positions, authenticates both halves of each
queried pair, checks consecutive folds and evaluates the final polynomial.
The source uses ordinary protocol calls, loops and installed mathematical and
oracle operations. No FRI-specific compiler or Host dispatch is involved.
From the repository root, with built tools on `PATH`:

```sh
zkc compile \
  --project=examples/projects/fri/zkc.toml \
  example::Proof --output=fri.zkpkg
```

That command selects the clear-table interpretation. To use the installed
octic Keccak Merkle realization with individual leaves, select it explicitly:

```sh
zkc compile \
  --project=examples/projects/fri/zkc.toml \
  '--oracle-realization={"format":"zkc.oracle-selection/0","roots":{"kind":"uniform","table":{"scheme":"rows.merkle-keccak256.koala-bear.ext8-binomial3/0","grouping":"individual","order":"natural"}},"order":"after-final-draw","authentication":"atomic-blocks"}' \
  example::Proof --output=fri-merkle.zkpkg
```

These packages retain the same logical protocol and have different deployment
identities. Use the same package and its digest for proof production and
verification. Merkle responses contain the complete rows and paths for both
fold children; they do not reuse the former specialized FRI sibling omission.

`Fri` provides its default interactive run entry without an `entry fn` wrapper.
`Proof` explicitly derives verifier randomness through
the installed Merlin3 transcript construction. Public inputs are the coset
`shift`, `round_count = 3` and `query_count = 8`; the verifier checks those counts
against the static profile. The prover supplies the `word` vector. Extension
values use the canonical eight-coordinate wire encoding. The test constructs
requests and polynomial words through independent integer arithmetic. Run its
regression suite from the repository root with the development environment:

```sh
uv run --no-sync --locked pytest common/tests/protocol/test_fri.py
```

The library also returns the sampled positions and their authenticated initial
word values. A surrounding polynomial-opening protocol must bind those values
to its own opening equations. This client demonstrates FRI execution and
rejection checks. The independent Lean model proves completeness on codewords
and round-by-round soundness of the library's low-degree test with ideal
commitments, including an interactive bound in the unique-decoding regime at
these parameters
([FRI security](../../../lean/docs/spec/fri-security.md)); this client
does not supply an AIR reduction, commitment security, a Fiat–Shamir security
theorem for its compiled verifier or zero knowledge.

## Executable quick start

Run these literal commands from this project directory with `zkc` and
`zkc-compile` on `PATH` (Python 3 for generated inputs). The test suite runs
this block in a separate consumer tree using only declared package dependencies.

```sh zkc-example
python3 prepare.py --output=build/inputs
zkc check
zkc run Fri --input=build/inputs/arguments.json
zkc prove Proof --public=build/inputs/public.json --witness=build/inputs/witness.json --output=build/fri.proof
zkc verify Proof --public=build/inputs/public.json --proof=build/fri.proof
```

Inputs: prepare.py deterministically evaluates 1 + 2X + ... + 8X^7 on 32 natural-order coset points.

Profile: KoalaBear octic extension; shift 3, degree below 8, three folds, eight queries. These are demonstration parameters.

Expected negative controls: A zero coset shift stops admission; altered terminal coefficients are refused. An authenticated realization additionally checks complete Merkle replies against the selected roots.

Generated packages, proofs and result documents are written under `build/`
inside this project. Existing input maps remain source inputs.
