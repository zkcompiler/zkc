# Monero Bulletproofs+

An aggregated range proof for two 64-bit amounts, using the reusable
[Bulletproofs+ library](../../../libraries/arguments/bulletproofs/README.md). `main.zkc`
selects its `Range` protocol and Monero transcript/proof format.

From this directory with built tools on `PATH`:

```sh
zkc check
zkc prove --allow-authored
zkc verify --allow-authored
```

`--allow-authored` authorizes the selected library's byte construction. It does
not certify cryptographic security. Proof and input paths follow the normal
[Entry layout](../../../docs/runtime/entries.md).

The public input contains the original commitment bytes and the folding-round
count: `6 + ceil(log2(number_of_commitments))`. Each participant checks that
count. The witness contains amounts `0,1` and masks `17,18`. The common Host
supplies fresh private randomness; the source code never exposes a coin tape.
The example masks are public test values and must not be reused in an application.

For new statements, call `monero::bulletproofs_plus::commit(values,masks)` or supply
Monero commitment bytes. There are 1..16 amounts; each is an unsigned 64-bit
integer. The proof object is byte-compatible with the pinned Monero version
specified in the library. It excludes the commitments and the rest of a Monero
transaction. The example runs through the ordinary compiler and proof Host.

## Executable quick start

Run these literal commands from this project directory with `zkc` and
`zkc-compile` on `PATH` (Python 3 for generated inputs). The test suite runs
this block in a separate consumer tree using only declared package dependencies.

```sh zkc-example
zkc check
zkc prove Proof --allow-authored
zkc verify Proof --allow-authored
```

Inputs: inputs/example.Proof/{public,witness}.json.

Profile: Monero Bulletproofs+ with 64-bit values and 1..16 commitments; randomness comes from the managed source.

Expected negative control: A wrong witness, zero challenge, malformed proof or changed commitment is refused.

Generated packages, proofs and result documents are written under `build/`
inside this project. Existing input maps remain source inputs.
