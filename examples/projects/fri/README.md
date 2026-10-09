# Binary FRI

This client runs the reusable [`fri::LowDegree`](../../../libraries/fri/lib.zkc)
protocol over the KoalaBear degree-eight extension field and authenticated
Merkle rows. It tests a word of 32 evaluations on a nonzero two-adic coset for a
polynomial of degree below 8, using three folds and eight queries. These small
parameters exercise the implementation; they are not a security recommendation.

The prover commits each word before receiving its folding challenge. After the
last fold it sends coefficients of a constant polynomial. The verifier checks
the degree bound, draws all query positions, authenticates both halves of each
queried pair, checks consecutive folds and evaluates the final polynomial.
The source uses ordinary protocol calls, loops and installed mathematical and
oracle operations. No FRI-specific compiler or Host dispatch is involved.

```sh
zkc compile --module=example=examples/projects/fri/main.zkc \
  --module=fri=libraries/fri/lib.zkc --entry=example::Proof --output=fri.entry
```

`Run` exposes interactive execution. `Proof` derives verifier randomness through
the installed Merlin3 transcript construction. Public inputs are the coset
`shift`, `round_count = 3` and `query_count = 8`; the verifier checks those counts
against the static profile. The prover supplies the `word` vector. Extension
values use the canonical eight-coordinate wire encoding. The test constructs
requests and polynomial words through independent integer arithmetic:

```sh
uv run --no-sync --locked pytest tests/protocol/test_fri.py
```

The library also returns the sampled positions and their authenticated initial
word values. A surrounding polynomial-opening protocol must bind those values
to its own opening equations. This client demonstrates FRI execution and
rejection checks; it does not supply an AIR reduction, a FRI proximity theorem,
a Fiat–Shamir security theorem or zero knowledge.
