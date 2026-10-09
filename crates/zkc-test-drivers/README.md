# Native integration drivers

These binaries exercise the public Rust SDK against compiler-generated programs.
Python tests in `tests/protocol/` generate artifacts and supply each driver's
arguments. `zkc-test-support` owns shared reference fixtures and evidence storage.

Build with `just build-test-drivers` or
`cargo build --release -p zkc-test-drivers --bins`. Drivers are installed directly
in the selected native binary directory, alongside the separately built `zkc`.
Their manifests explicitly enable deterministic test providers. The product build
selects only `zkc-tools` with default features; Nix packages each build separately.

The small library adapts positional test records to the typed proof SDK. Drivers
remain test clients and do not provide a second execution implementation.
