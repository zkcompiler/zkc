# Edwards map vectors

`edwards-map.json` contains input/output pairs from Monero
`4f92268d7c16741cfb41e5bbe2aa46cc260a9ea5`'s
`ge_fromfe_frombytes_vartime`, followed by `ge_mul8` and compression.
The 137 inputs cover zero, one, field boundaries, the high input bit and
SHA-256 digests of decimal indices 0..127. The [independent producer](../../../../common/tests/reference/monero/README.md)
regenerates them without calling zkc.
