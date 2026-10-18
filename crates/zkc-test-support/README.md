# Native test support

This crate owns immutable conformance fixtures, variant declaration helpers,
bounded JSON-lines probe transport, hexadecimal helpers and retained test evidence.
`source(name)` resolves a fixture under this crate's `fixtures/` directory.
`ZKC_REPORTS_DIR` selects the evidence root; each test process reserves an exclusive
run directory so concurrent executions cannot erase one another's reports.

The external-transcript fixture metadata records upstream provenance and expected
results. These fixtures are shared by backend tests and native transcript examples.
No compiler or Lean checker is launched by this support crate.

`fixtures/native-proof-binding.json` fixes one native proof invocation tree and
its literal binary encoding, SHA-256 digest and byte length. The bytes are independently
framed from the specified array/string preorder grammar (one tag byte, an
eight-byte little-endian count, then contents), without a compiler or runtime
serializer. Host tests compare actual prepared bytes and proof headers to this
vector. Regenerating it from production serialization would erase that check.

`fixtures/transcript-vectors.json` fixes the framed Spongefish Keccak duplex
requests, 64-byte outputs and big-endian Fr reductions. Its current suite uses
Spongefish 0.8.0. The outputs were independently evaluated with the Keccak-f[1600]
permutation and overwrite-mode duplex (136-byte rate), after reproducing the
previous frozen vector and the zero-state XKCP permutation vector. Suite-name
changes alter absorbed bytes and require independent vector regeneration.

`fixtures/hash-chain-vectors.json` fixes the native hash-chain suites' states,
request answers and decoded challenges for one binding root and fixed
occurrences. It is the output of the independent Python reference
`common/tests/support/hash_chain_reference.py`, whose own Keccak-f[1600] is
checked against published Keccak-256 answers and Python's SHA3-256; the
integration suite checks that the file equals the reference's output.
