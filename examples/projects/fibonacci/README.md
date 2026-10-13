# Fibonacci STARK

Prove eight rows of `(x,y) -> (y,x+y)` over KoalaBear, from `(0,1)` to `(13,21)`.
The project has two proof Entries: `CleanProof` imports a locally authored Clean table;
`Plonky3Proof` imports an independently authored Plonky3 AIR. Both call the same
[`TableArgument`](../../../libraries/stark/README.md) protocol.

With built tools on `PATH`, run here:

```sh
zkc check
zkc prove CleanProof
zkc verify CleanProof
zkc prove Plonky3Proof
zkc verify Plonky3Proof
```

The public inputs are the two boundary states; the private input is the trace.
`prepare.py` regenerates the committed sample input maps from the external
adapter fixtures; `prepare.py --check` checks that they agree. `zkc prepare`
creates input templates for your own invocation without replacing values.

See the [Clean adapter](../../../compiler/adapters/clean/README.md) and
[Plonky3 adapter](../../../compiler/adapters/plonky3/README.md) for source pins
and regeneration. The tests compare both traces against an independent integer
recurrence, reject mutations and prove/verify both source Entries.
The Clean client uses `TableConstraint` and its witness generator; it does not
provide an upstream `FormalTable` specification or a correctness theorem.

These are small test parameters and nonhiding commitments. The proof uses zkc's
format and transcript; it is not a Plonky3 proof-format compatibility example.
