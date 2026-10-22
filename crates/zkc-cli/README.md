# zkc command-line application

The `zkc-cli` package installs the `zkc` binary. It owns command arguments,
help, human and JSON rendering, project recipe execution and command
orchestration. It calls the [zkc SDK](../zkc/README.md) for compilation,
authenticated package admission, input decoding, preparation and execution.
Applications embedding precompiled packages depend on `zkc` directly and need
neither this binary nor the compiler.

Build with `cargo build -p zkc-cli --bin zkc`. Instrumentation requires the
explicit `execution-counts` feature. Test providers are off by default.
Use `zkc --help` and `zkc COMMAND --help` for commands, defaults and recipes.
