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
| `recursive-records.mlir` | `4c2780e9e5f46f74e3747c821aeeb46a5c026193e516324487bd4886389dce01` |
| `recursive-records.json` | `48e026555553df1536459e67070e4824670d0e5a6976d4d25491640d401b15f0` |
| `custody-records.mlir` | `ba92e5aaafcdca2cb352b9222ad0443a5d623747b4638973961a27e94555c881` |
| `custody-records.json` | `a234ecad6f45348fc5960dfcf73e35735af0e9afdc6e8f32659e88bb4d5c1ee2` |
| `schema-digests.json` | `2ff489fd74b2f3625b59511adf10c309de51fb03529f534f6615c92988ad6e16` |
