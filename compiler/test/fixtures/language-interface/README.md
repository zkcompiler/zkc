# Recursive interface consumer fixtures

These are independent native/interface fixtures for the current strict
[`zkc.language-interface/0`](../../../../docs/spec/formats/entry.md) schema.
`language_recursive_interface.cpp` constructs actual native protocol IR and
static declaration metadata without fabricating a checked source project.
They test independent structural/native admission; they do not claim source
correspondence or new formal proofs.

`zkc-language_recursive_interface-test` writes the exact positive pairs when
given this directory. [The interface fixture script](../../../../scripts/regenerate-interface-fixtures.py)
runs it, together with the other compiler-produced interface fixtures, from a
named compiler build and recomputes the digest table below:

```sh
python3 scripts/regenerate-interface-fixtures.py build/compiler
```

The original digest covers the exact `.mlir` bytes, including their printing
policy. The toolchain digest records the producing compiler build. The
compiler's interface reader admits only its own live identity, so a consumer
testing schema structure independently takes the toolchain digest as a fixture
parameter, and must not treat that as native/source authentication. A compiler
edit that changes only that identity needs no regeneration; a change to the
schema, the native printing or these constructions does.

`schema-digests.json` records full root schema hashes for cross-reader checks;
`custody-records.*` retains a two-role wrapper prefix and a nested ordinary prefix.
Each retained declaration carrier lists one authority row per nominal path at a
fixed fixture revision, and every schema identity and custody slot hashes that
nominal's canonical key over those rows, as a checked source would.

The authored `.zkc` fixture separately exercises checked source, a reordered
callee roster and source/native correspondence. Its test is
`language-record-interface-source` (or run the executable with `--source` and
that fixture path). It requires the source placed-record and native transport
commits together; the interface slice alone does not establish that integration.

The recursive record pair covers two independently held equal-kind handles,
a nested role application whose arguments permute the outer telescope, shared
receiver anchor coordinates, a private zero-length logical array, its complete
element schema and its one placement template. A zero logical array is not an
ordinary empty payload.

The C++ test mutates component coverage, order, path, local leaf, role, facet and
native coordinate; record identity, argument arity/aliasing, child order and
formulas; privacy and repeated schemas; required-nullable members, zero-array
elements and custody counts. Separate native mutations cross equal-typed actual
input anchors and output pairs. Public/selector/setup controls select an ordinary
field at its own role, distinguish receiver anchors from verifier-held data,
route nested verifier/prover keys independently, and reject private, overlapping,
whole-logical and incomplete setup selections. Distributed and nested ordinary custody fixtures
exercise separate prefix counts and role-order mappings.

Independent Rust/Lean consumers must migrate these exact shape changes together:

- Replace port `roles`/`holder` with required `placement` and `components`.
  Only direct handles retain required-nullable `maximum_rows`.
- Decode schema `custody` as an unsigned integer. Require declaration `roles`,
  required-nullable `element`, required-nullable `generated`, and Boolean
  `sealed` independent of custody and constructibility.
- Every field requires Boolean `public` and required-nullable `placement`.
  Preserve conditional direct unsized-handle `maximum_rows`.
- Reconstruct logical category through tuples and zero-array elements; preserve
  complete nominal telescopes, child formulas and ordered role substitutions.
- Require external product instances to equal schema identity digests exactly.
  Canonicalize structural argument unions after substitution, preserving nominal
  argument order. Components are ordered by field, body leaf, participant.
- Retained source declaration rows keep their existing shape but admit nested
  distributed/resource records. Every referenced nominal type must be retained;
  ordinary carriers reject logical category even in phantom or zero-array types.
  Sealing is independent of the linear/affine resource restriction.
- Include generated family identity, integer custody, telescope, element,
  associated data, privacy and formulas in the full schema hash. The shared
  format specifies the exact frame order; sealing follows custody and precedes
  constructibility.
- Proof jobs retain exact `{port,path,role}` public selections, including empty
  ordinary coverage. Integer whole-port lists are refused. The
  [ordinary component fixtures](../entry-components/README.md) retain fresh
  source/native/interface pairs and generated Host-family controls.

A consumer still requiring Boolean custody, a root holder, or the former schema
member set is incompatible with this fixture. That reader migration is a landing
gate. C++ tests and fixture admission establish no Lean connector or theorem.

## Current fixture SHA-256

These hashes cover the exact retained bytes from the generator above.

| File | SHA-256 |
|---|---|
| `recursive-records.mlir` | `8738677e7602e5ed32684b4b35acfabca64e47cb1a5ea79eff0741c60543bd68` |
| `recursive-records.json` | `1d18d7ee9a17908f272547fda7c8d4ed13c11d891a948e206d92bb73057ee633` |
| `custody-records.mlir` | `cc6e2a54136ba37bd08c766bf5d9c543849a0606f55dcc991d363575b0572e60` |
| `custody-records.json` | `5d49352950fe8328691af351975f9edaf51325186cd541e2246514e49c28a8d0` |
| `schema-digests.json` | `e728c5bbc84eaf3ed9c60b430e42f53122520558d7554a3a1c35be00bb348633` |
