# zkc-catalog

Static typed metadata projected from the [shared declaration source](../../common/catalog/README.md).
The crate has no runtime dependencies and does not depend on MLIR or an execution
backend. Its build script independently validates and projects the source using
Rust build dependencies only. Generated files stay in Cargo's output directory.

The table is declaration data. Consumers still check actual arguments, profile
admission, domain capabilities, installation and effects. Mathematical facets
state obligations; they are neither implementation evidence nor generated proofs.

Run `cargo test -p zkc-catalog` for schema and semantic mutation controls.
