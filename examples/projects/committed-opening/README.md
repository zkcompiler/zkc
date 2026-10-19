# Committed opening

The smallest protocol with a committed table: the prover commits a table of
`2^LogRows` KoalaBear rows of `Width` values with the installed Keccak-256
Merkle scheme `rows.merkle-keccak256.koala-bear/0` and sends its root. The
verifier draws one position with `coins.index<pow2(LogRows)>()`, the prover
opens the row there and sends the row and its authentication path, and the
verifier checks the opening with `oracle::check` against the received root at
its own position, width and height before testing the row. A row `(a, b, c)`
passes when `c = a * b`.

The scheme, the height and the width are fixed by the program (the Entry
instantiates `CommittedOpening<3, 3>`: eight rows of three values), so the
prover supplies only the root, the row and the path. The proof Entry derives
the position from the installed hash-chain transcript
`hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0`, whose
challenge field supports index requests. The protocol draws no field element,
so its one request has a fixed shape. The row and path follow the last request:
they are terminal messages, which the native construction absorbs like every
other message.

```sh
zkc prove example::Proof
zkc verify example::Proof
```

The witness in `inputs/example.Proof/witness.json` is the honest table
`(i + 1, i + 2, (i + 1)(i + 2))` for `i < 8`. A proof for a table whose rows
fail the predicate is produced but rejected, and changing the root, a row
value or a path digest in the proof bytes makes verification stop with
`reject`.

One position tests one row, so a prover whose table has a fraction `δ` of
failing rows is accepted with probability about `1 - δ` per attempt. The
example exercises the compiled path of index requests, row commitments and
terminal openings; it is not a useful soundness level, and it makes no
security claim. The [formal model](../../../lean/docs/spec/fiat-shamir-security.md#verifiers-with-committed-tables)
of this verifier is a separate transcription, not the compiled Entry.
