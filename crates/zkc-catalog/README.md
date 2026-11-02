# zkc-catalog

Static typed metadata projected from the [shared declaration source](../../common/catalog/README.md).
The crate has no runtime dependencies and does not depend on MLIR or an execution
backend. Its build script independently validates and projects the source using
Rust build dependencies only. Generated files stay in Cargo's output directory.

The build reads two inputs of one catalog package: `declarations.json`
([`zkc.contract-declarations/0`](../../docs/spec/formats/contract-declarations.md))
and `installation.json`
([`zkc.native-installation/0`](../../docs/spec/formats/native-installation.md)),
which references the first one way. Both are validated together.

The installed-instance tables (domains, logical type instances, frame tags,
codecs, aggregate frames, random services, limits and the source vocabulary)
join `CATALOG` in declared order. The native installation document is the
separate `INSTALLATION` static, so a physical-only change leaves the logical
projection unchanged. `DomainIdentity` enumerates exactly the declared domains:
`name()` returns the canonical identity and `parse` accepts only that spelling.
Variant names are presentation only, and identities whose presentations
coincide are refused at build time. These rows declare which instances, codecs
and physical choices exist; they grant no execution, transport or handler, and
a target still admits each implementation it runs.

`tests/installed.rs` checks that every authored row and fact reaches the
projection in order. `tests/validation_cases.rs` runs the
[shared validation cases](../../common/catalog/README.md). The runtime, the CPU
backend and the SDK read these tables; the `installed_parity` tests of
`zkc-runtime` and `zkc-cpu` keep their Rust names of domains, constructors,
representations, services and implemented suites a bijection with the rows.

`limit`, `codec_tag`, `instance_tag` and `aggregate_frame_tag` are `const`
lookups, so a constant derived from a row fails the build when the row is
removed or loses its frame.

Runtime admission interprets the table's kinded scopes, signatures, requirements,
parameter rules, history facets and type permissions. Consumers still check actual arguments, profile
admission, domain capabilities, installation and effects. Mathematical facets
state obligations; they are neither implementation evidence nor generated proofs.

`Facet::DeterministicData` projects the explicit nullary `DeterministicData`
catalog facet. It relates equal complete logical inputs and parameters to equal
normal results or the same logical stop for an installed exact admitted
interpretation. Partial operations retain their stops; the facet grants no
totality, speculation, budget equality or private-service authority. Consumers
still admit exact bindings and closed functions, recursively check immutable
data, and establish selected implementations independently of the unselected
interpretation. `Facet::PublicReplay` remains a separate restricted total
public-construction contract. Unknown or unclassified operations gain neither
fact.

`Facet::Succession` projects a resource identity transfer: the output is the
successor of the exact `resource_unit` received at the input, with the same
Slot root, and the signature has no other `resource_unit` port. It grants no
value equality, purity, reordering or speculation.

`CATALOG.consumer_profiles` and the exact-name `consumer_profile` /
`consumer_profile_operation` queries expose explicit owner-fixed enrollment and
kinded formal roots. The generator checks each entry against its independently
authored declaration expectation, including associated scope, ordered ports,
requirements and parameter schema. These queries do not validate a binding or
extend backend/interpreter support. The initial `structured-source-primitives`
profile requires unselected implementations and retains sixteen data operations
plus the three nominal resource-unit operations with exact Slot roots.

Run `cargo test -p zkc-catalog` for schema and semantic mutation controls.
