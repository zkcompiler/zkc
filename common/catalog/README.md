# Shared declaration source

`declarations.json` is authored neutral data, not a generated snapshot. It owns
the built-in declaration facts in [`zkc.contract-declarations/0`](../../docs/spec/formats/contract-declarations.md).
Edit this source when changing identities, kinded signatures, requirements,
permissions, mathematical or operational facets, or owner-fixed consumer profiles. Array order is declaration order; nominal
identity determines meaning. No row installs executable code or a formal interpretation.

The compiler's configure step checks exact JSON shapes and projects ordinary
TableGen records. `zkc-tblgen` independently checks declaration formation before
generating native C++ data and MLIR adapter inputs. The Rust `zkc-catalog` build
checks the same source independently and emits static typed tables in `OUT_DIR`.
Rust does not run Python or LLVM; the compiler does not run Cargo. Generated
records and tables are build outputs and are not checked in.

The source format is intentionally explicit. Scope references, signature-family
tags and facets remain data rather than authoring-class privileges. Backend
installation, executable behavior and supported interpretation profiles have
their own owners. Native contribution declarations are separately admitted and
are included in the installed exported inventory; adding one does not silently
change the built-in Rust installation.

`DeterministicData` is an explicit nullary operational facet. For the same
installed exact admitted implementation, equal complete logical inputs and
parameters have equal normal results or the same logical stop. It includes
partial operations and grants no totality, speculation, budget equality,
randomness/security theorem, mutable-state or private-service authority. Its
native projection is `OperationContracts::deterministicData` (default false);
its Rust projection is `Facet::DeterministicData`. The neutral export is exactly
`{"kind":"DeterministicData"}` in `zkc.contract-declarations/0`.

Rows are finite and explicit: new operations never inherit this facet by name
or prefix. A selected/custom implementation does not inherit the unselected
interpretation. Consumers still check exact bindings, types, parameters and
closed functions, including recursive container immutability and every stop
path. This interpretation is independent of mathematical meaning, purity and
Copy. `PublicReplay` retains its separate restricted total public-construction
contract. See the [owning semantics](../../docs/spec/formats/contract-declarations.md#deterministic-data).

`consumerProfiles` explicitly selects operations for a named consumer. Each
entry pins the consumed declaration shape separately; generation rejects drift
in scope, stage, ordered signature, requirements or parameter schema. Update an
expectation only after its consumer owner accepts that contract. Adding a
declaration or contribution never enrolls it into an existing profile. The first
profile, `structured-source-primitives`, preserves the structured exporter's
sixteen primitive identities and its unselected implementation policy.

Build-free source controls and TableGen input regeneration:

```sh
python3 common/catalog/test_profiles.py -v
python3 common/catalog/test_deterministic_data.py -v
python3 common/catalog/generate.py --source common/catalog/declarations.json --output build/compiler/include/zkc/Contracts
```

`Catalog.td` and `Mathematical.td` are generated outputs. The normal compiler
configure step runs this projection; the `ZkcContractDeclarationsGen` target
then regenerates native `Declarations.cpp.inc` using `zkc-tblgen`. Cargo
regenerates its own `OUT_DIR/catalog.rs` when the source or Rust generator
changes. None of these outputs is authored source or belongs under `lean/`.
