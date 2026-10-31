# zkc-catalog

Static typed metadata projected from the [shared declaration source](../../common/catalog/README.md).
The crate has no runtime dependencies and does not depend on MLIR or an execution
backend. Its build script independently validates and projects the source using
Rust build dependencies only. Generated files stay in Cargo's output directory.

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

`CATALOG.consumer_profiles` and the exact-name `consumer_profile` /
`consumer_profile_operation` queries expose explicit owner-fixed enrollment and
kinded formal roots. The generator checks each entry against its independently
authored declaration expectation, including associated scope, ordered ports,
requirements and parameter schema. These queries do not validate a binding or
extend backend/interpreter support. The initial `structured-source-primitives`
profile requires unselected implementations and retains its sixteen operations.

Run `cargo test -p zkc-catalog` for schema and semantic mutation controls.
