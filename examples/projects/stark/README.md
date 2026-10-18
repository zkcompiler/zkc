# Parameterized STARK

Prove the eight-row Fibonacci AIR of the [Fibonacci project](../fibonacci/README.md)
with the parameterized single-table STARK library,
[`stark::argument::TableArgument`](../../../libraries/stark/README.md#parameterized-single-table-argument).
`CleanProof` imports the Clean table and `Plonky3Proof` the Plonky3 AIR; the
inputs are the Fibonacci project's.

Both Entries select the configuration `stark::koala_bear::quartic::Poseidon2`:
KoalaBear trace rows, quartic-extension challenges, quotient and FRI, width-16
Poseidon2 Merkle trees with pruned multi-openings, natural-order rows with both
FRI fold siblings in one leaf, and the Merlin KoalaBear transcript suite. The
static arguments choose the FRI shape: `LogFinal = 0` and `Rounds = 3` give the
trace height 8, `LogBlowup = 2` gives 32 evaluation points, and `Queries = 8`.
These are small testing parameters, without a security claim.

With built tools on `PATH`, run here:

```sh
zkc check
zkc prove Plonky3Proof
zkc verify Plonky3Proof
zkc prove CleanProof
zkc verify CleanProof
```

The proof carries the trace and quotient roots, the out-of-domain claims, one
root per FRI round and the final polynomial, then, after every query position
has been drawn, one pruned multi-opening of the trace rows, of the quotient rows
and of each FRI layer. The verifier receives only the sibling of each FRI pair;
it reconstructs the leaf from its own value. The proof is about 2.3 KB, against
13.5 KB for the same AIR and sizes through the Fibonacci project's profile.

The [library tests](../../../common/tests/protocol/test_stark_library.py)
prove these Entries under several compilation modes, alter every proof message,
change public inputs, open wrong rows, run two dishonest provers, and repeat
the protocol with a bit-reversed configuration. Commitments are nonhiding and
the proof format is zkc's own, not Plonky3's.
