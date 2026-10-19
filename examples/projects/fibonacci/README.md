# Fibonacci STARK

Prove eight rows of `(x,y) -> (y,x+y)` over KoalaBear, from `(0,1)` to `(13,21)`.
The project has two proof Entries: `CleanProof` imports a locally authored Clean table;
`Plonky3Proof` imports an independently authored Plonky3 AIR. Both call the same
[`TableArgument`](../../../libraries/arguments/stark/README.md) protocol.

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

## Executable quick start

Run these literal commands from this project directory with `zkc` and
`zkc-compile` on `PATH` (Python 3 for generated inputs). The test suite runs
this block in a separate consumer tree using only declared package dependencies.

```sh zkc-example
zkc check
zkc prove CleanProof
zkc verify CleanProof
zkc prove Plonky3Proof
zkc verify Plonky3Proof
```

Inputs: inputs/ contains both adapter witnesses and public boundaries; prepare.py regenerates them in a checkout.

Profile: The fixed octic table argument consumes independently captured Clean and Plonky3 relations.

Expected negative control: Changing a public boundary or a trace opening refuses verification.

Generated packages, proofs and result documents are written under `build/`
inside this project. Existing input maps remain source inputs.
