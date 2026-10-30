# zkc-format

Provider-free syntax and byte formats shared by package consumers and execution:

- `logical`: canonical logical trees, encodings and occurrence descriptors.
- `proof`: selected proof framing and bounded, lazy frame reading.
- `binding`: immutable invocation binding serialization and hashing.
- `types`: bounded canonical graphs for native variant spellings.

These readers do not admit native programs, authenticate a package, select a
provider or grant resource authority. The runtime owns execution and metered
transport; the CPU backend owns installed value codecs. Extracted implementations
retain their existing version-zero bytes.

Run `cargo test -p zkc-format` for the standalone format checks.
