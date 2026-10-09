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
