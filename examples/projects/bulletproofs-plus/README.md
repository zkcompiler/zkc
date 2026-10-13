# Monero Bulletproofs+

An aggregated range proof for two 64-bit amounts, using the reusable
[Bulletproofs+ library](../../../libraries/bulletproofs/README.md). `main.zkc`
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

For new statements, call `bulletproofs::monero::commit(values,masks)` or supply
Monero commitment bytes. There are 1..16 amounts; each is an unsigned 64-bit
integer. The proof object is byte-compatible with the pinned Monero version
specified in the library. It excludes the commitments and the rest of a Monero
transaction. The example runs through the ordinary compiler and proof Host.
