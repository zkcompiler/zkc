# Bulletproofs+ controls

`corpus.json` contains 64 independent Monero proofs: every aggregation count
from 1 through 16, each with zero, maximum-u64, alternating boundary and seeded
random amounts. It records original commitment bytes, amounts, masks, replayed
private coins and complete serialized proof bytes. The owning revision is in
the file; see the [upstream reproduction](../../reference/monero/README.md).

The recorded coins are public test data, never suitable for deployed proofs.
Generate these fixtures from the upstream executable, never from zkc.
