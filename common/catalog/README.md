# Shared declaration source

The catalog package is two authored documents, neither of them a generated
snapshot:

- `declarations.json` owns the built-in declaration facts in
  [`zkc.contract-declarations/0`](../../docs/spec/formats/contract-declarations.md):
  identities, kinded signatures, requirements, permissions, mathematical or
  operational facets, owner-fixed consumer profiles, and the
  [installed-instance tables](../../docs/spec/formats/contract-declarations.md#installed-instances)
  (domains, logical type instances, frame tags, codecs, aggregate frames,
  random services, limits and the source vocabulary).
- `installation.json` owns the physical choices in
  [`zkc.native-installation/0`](../../docs/spec/formats/native-installation.md):
  representations, provider preferences and units, field forms and backend
  calling conventions. Its rows reference declaration keys; the declarations
  never reference it.

Array order is declaration order; nominal identity determines meaning. Every
row is explicit: no identity is formed by concatenation, a family or a loop. No
row installs executable code or a formal interpretation.

Three validators check both documents independently. The compiler's configure
step runs `generate.py`, which checks every rule of both chapters on the JSON,
including the cross-document references, and projects ordinary TableGen records:
`Catalog.td` holds the logical declarations only and `NativeInstallation.td`
holds the physical records. `zkc-tblgen` checks the same rules again over those
records before generating native C++ data, MLIR adapter inputs and the
installed-instance tables (`zkc/Contracts/Instances.h`); its
`-dump-contract-declarations` and `-dump-native-installation` actions each print
only their own document. The Rust `zkc-catalog` build checks the same sources
independently and emits static typed tables in `OUT_DIR`. Rust does not run
Python or LLVM; the compiler does not run Cargo. Generated records and tables
are build outputs and are not checked in.

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
sixteen data primitive identities plus the three nominal resource-unit
operations, with its unselected implementation policy. Slot roots retain their
exact nominal identities and do not enroll algebraic domains. Independent
formal-consumer support is tracked separately.

Build-free source controls and TableGen input regeneration:

```sh
python3 common/catalog/test_profiles.py -v
python3 common/catalog/test_deterministic_data.py -v
python3 common/catalog/test_instances.py -v
python3 common/catalog/generate.py --source common/catalog/declarations.json \
  --installation common/catalog/installation.json --output build/compiler/include/zkc/Contracts
```

`test_instances.py` validates both documents, refuses forged rows, and compares
the data with the independently authored Python oracles of the EVM wire,
foundation, binomial and hash-chain references without changing them.

`validation-cases.json` is the case list shared by the three validators: edits
of the two documents that each validator must accept, and edits that each must
refuse, with the diagnostic each one gives. `validation_cases.py` specifies and
applies the edits. `test_instances.py` runs them against the generator, the
compiler's `catalog-source` test against the generator and `zkc-tblgen`, and
`crates/zkc-catalog/tests/validation_cases.rs` against the Rust build.

`Catalog.td`, `Mathematical.td` and `NativeInstallation.td` are generated
outputs. The normal compiler configure step runs this projection; the
`ZkcContractDeclarationsGen` target then regenerates native
`Declarations.cpp.inc` and `Instances.inc` using `zkc-tblgen`. The compiler's
`installedDomains()`, `plonky3Fields()` and applied representations are built
from the installed-instance and installation tables through the validating
`DomainCatalog` constructor. The `installed-instances` test retains an ordered
dump of these owners and of the facts their consumers derive, in
`compiler/test/fixtures/contracts/installed-instances.json`, and compares the
remaining restatements with the tables. Cargo
regenerates its own `OUT_DIR/catalog.rs` when the source or Rust generator
changes. None of these outputs is authored source or belongs under `lean/`.

`frontendAssociations`, `frontendHomes` and `serviceMethods` own source
intrinsic/service signature rules and semantic constructor homes. Native and
Rust generation independently reject forged rules, unknown fields, duplicate
owners and capability drift. Installed source declarations are separately
checked against their marker signatures; captured homonyms grant no authority.
See [frontend associations](../../docs/spec/formats/contract-declarations.md#frontend-declaration-associations).
