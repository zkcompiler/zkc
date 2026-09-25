# Separately authored protocol projects

Each `main.pir` consumes its matching library under `../libraries/`. A library's
identity is declared in source; `--library` maps that identity to a root file.
For example, from the repository root:

```sh
build/compiler/zkc-compile protocol-source examples/projects/group/main.pir \
  --library=examples/libraries/group/lib.pir
build/compiler/zkc-compile protocol-construct examples/projects/group/main.pir \
  examples/projects/group/main.construction.pir \
  --library=examples/libraries/group/lib.pir
```

| Project | Actual path | Boundary |
|---|---|---|
| `groth16` | Existing BN254 Groth16 arithmetic, generated R1CS products/residuals, restricted bound/satisfied assignment constructors | The checked native host supplies actual snarkjs keys/witnesses; ceremony and C/IC/H/query derivation remain premises |
| `pcs` | Compiled ordinary multilinear KZG opening check | Native setup/index checks retain exact relation/public layout, encoding and dimensions; `CheckedIndex` is never a PIR input |
| `air` | Complete maintained N=8 AIR permutation, quotient/OOD, Merkle openings and FRI | Same bounded experimental argument as the original; no new security-bit or hiding claim |
| `group` | Client-selected BLS component for a scalar draw, group multiplication and equality over a generic group interface | RNG is affine; source construction selectors name owner-qualified declarations |
| `views` | Abstract finite traversal over unit/pair private layouts, finite errors and a selected terminal implementation | Local non-polynomial views, not a new proof system; zero storage still carries affine permissions |

`pcs`, `group`, and `views` include independently authored concrete `closed.pir`
controls. Groth16 and AIR use the existing closed sources under `examples/protocols`
as independent importer controls. The library copies retain the existing arithmetic;
the test does not reconstruct the baseline by removing imports from its own output.

Run the Python integration driver with matching prebuilt native and Lean tools:

```sh
uv run --no-sync --locked pytest -q tests/protocol/test_frontend_projects.py
```

The `zkc-tools` integration test `frontend_projects` drives the actual PCS native
preparation seam. Its Groth16 case additionally needs the existing pinned real fixture tree:

```sh
cargo test --locked -p zkc-tools --features test-utils --test frontend_projects
just test-groth16 /path/to/snarkjs-fixtures
```

The checked-in Groth16 `circuit.json` is a readable relation for source inspection,
not fake proving material. The real-fixture test copies this library into its own
evidence directory, replaces that asset with each real depth-2/depth-16 `.r1cs`,
and calls `PreparedProtocol::compile_project` before checked ingress and proving.
The library asset resolves relative to its declaring file, not to `main.pir`.

The Python records keep commands, sources, plans, observations, mutations and
bounded size/time measurements. These tests compare concrete runs and exact
refusals; they establish neither arbitrary-scale support nor a compiler proof.
