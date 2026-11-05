# Closed source-term fixtures

`descriptors.json` contains output of the public `encodeStaticTerm` C++ API.
The fixture test constructs closed candidate Types and uses the API's existing
Type preflight and strict wire validation. These are codec fixtures, not parsed
source, structural formation graphs or native protocol acceptance evidence.

Named rows retain primitive Finite bytes, ordered and reversed heterogeneous
Products, empty Product, unsized/zero/positive Sequences, nested structures and
ordinary tuple/array/formal/logical-record controls. The C++ test checks the
retained JSON against fresh public output. The independent Rust interface
static-argument tests read these same rows and assert their typed structure and
equality, including order and extent presence.

From the pinned development shell, with an assertion-enabled private build:

```sh
cmake --build build/compiler-dev --parallel 4 --target zkc-language_descriptor_source_terms-test
build/compiler-dev/test/zkc-language_descriptor_source_terms-test --emit-fixtures compiler/test/fixtures/source-terms/descriptors.json
ctest --test-dir build/compiler-dev -R '^language-descriptor-source-terms$' --output-on-failure
cargo test --locked --offline -p zkc --lib entry::interface::tests::static_arguments
```

The current production schema is the [protocol origin grammar](../../../../docs/spec/formats/structured-source.md#definition-origins).
Future installed leaf schemas and independent Lean reader migration remain
separate requirements. Fixture generation does not install leaf authority.

## Current fixture SHA-256

| File | SHA-256 |
|---|---|
| `descriptors.json` | `bd48aedf1f4a7b3014fa35bd1f3abefdff3df9489c9f6e05a7ca83190a956fca` |
