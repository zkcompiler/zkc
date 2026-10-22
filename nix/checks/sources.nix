# Guard meaningful package/check boundaries using the actual filtered trees.
{
  runCommand,
  python3,
  sources,
}:
runCommand "zkc-source-boundaries" { nativeBuildInputs = [ python3 ]; } ''
  set -x
  test -f ${sources.compiler}/compiler/CMakeLists.txt
  test -f ${sources.compiler}/common/unicode/generate.py
  test ! -e ${sources.compiler}/compiler/test
  test ! -e ${sources.compiler}/common/tests
  test ! -e ${sources.compiler}/lean
  test -f ${sources.compilerTests}/common/tests/fixtures/clean/air-control.json
  test -f ${sources.compilerTests}/compiler/test/CMakeLists.txt
  test -f ${sources.compilerTests}/compiler/test/support/source_project.py
  test -f ${sources.compilerTests}/common/tests/support/project.py
  test -f ${sources.compilerTests}/libraries/protocols/polynomial/sumcheck/zkc.toml
  test -f ${sources.compilerTests}/common/tests/fixtures/projects/scoped-computations/main.zkc
  test ! -e ${sources.compilerTests}/common/tests/run.py
  test -f ${sources.rust}/crates/zkc-cli/Cargo.toml
  test -f ${sources.rustConsumer}/common/tests/check_rust_sdk.py
  test -f ${sources.rustConsumer}/common/tests/consumer/rust/main.rs
  test -f ${sources.rustConsumer}/common/unicode/manifest.json
  test ! -e ${sources.rustConsumer}/compiler
  test -f ${sources.rust}/crates/zkc/Cargo.toml
  test -f ${sources.rust}/crates/zkc-benchmarks/Cargo.toml
  test -f ${sources.format}/common/benchmarks/monero.cpp
  test ! -e ${sources.rust}/scripts
  test ! -e ${sources.rust}/compiler
  test ! -e ${sources.rust}/common/tests
  test -f ${sources.rustTests}/compiler/test/fixtures/relation/polynomial-chunks.json
  # Scope discovery must not require protocol-only project support.
  test ! -e ${sources.rustTests}/common/tests/support
  python3 ${sources.rustTests}/common/tests/run.py rust --help > /dev/null
  test ! -e ${sources.integration}/common/tests/harness
  test ! -e ${sources.integration}/common/tests/consumer
  test -f ${sources.integration}/docs/getting-started.md
  test -f ${sources.integration}/common/tests/protocol/test_rust_sdk.py
  test -f ${sources.integration}/common/tests/protocol/test_preparation_policies.py
  test -f ${sources.integration}/common/tests/protocol/test_library_packages.py
  test -f ${sources.integration}/common/tests/protocol/test_example_recipes.py
  test -f ${sources.integration}/examples/projects/fri/README.md
  test -f ${sources.integration}/libraries/constructions/ethereum/eip4844/example_vectors.json
  test -f ${sources.integration}/compiler/adapters/clean/adapter.py
  test -f ${sources.integration}/compiler/adapters/ring_arena.py
  test -f ${sources.integration}/compiler/adapters/clean/fixtures/femtocairo/bundle.json
  test -f ${sources.sdk}/common/tests/consumer/test_discovery.py
  test ! -e ${sources.sdk}/compiler/lib
  test ! -e ${sources.lean}/lean/integrations
  test -f ${sources.lean}/lean/checks/DeclarationRecords.lean
  test ! -e ${sources.lean}/lean/checks/check_records.py
  test -f ${sources.lean}/lean/ZkcTools/CommonSource.lean
  test -f ${sources.lean}/lean/ZkcExamples/NativePrograms/CustomProperty.lean
  test -f ${sources.leanChecks}/common/tests/fixtures/clean/air-control.json
  test -f ${sources.security}/lean/security/lake-manifest.json
  test ! -e ${sources.security}/lean/integrations/arklib
  test ! -e ${sources.arklib}/lean/integrations/clean
  test -f ${sources.arklib}/lean/checks/check_clients.py
  test -f ${sources.security}/lean/checks/check_library.py
  test -f ${sources.security}/lean/checks/check_package_ownership.py
  test -f ${sources.security}/lean/checks/audit_imports.py
  test -f ${sources.security}/lean/support/packages.py
  test -f ${sources.security}/lean/support/dependencies.py
  test -f ${sources.security}/lean/support/lean_headers.py
  test -f ${sources.arklib}/lean/checks/check_library.py
  test -f ${sources.arklib}/lean/checks/check_package_ownership.py
  test -f ${sources.arklib}/lean/checks/audit_imports.py
  test -f ${sources.arklib}/lean/support/packages.py
  test -f ${sources.arklib}/lean/support/dependencies.py
  test -f ${sources.arklib}/lean/support/lean_headers.py
  test -f ${sources.application}/libraries/core/traversal/finite.zkc
  test -f ${sources.application}/libraries/core/primitives/collections/sequence.zkc
  test -f ${sources.application}/common/tests/support/project.py
  test -f ${sources.application}/libraries/protocols/sigma/schnorr/zkc.toml
  test -f ${sources.application}/zkc.workspace.toml
  test -f ${sources.integration}/zkc.workspace.toml
  test -f ${sources.libraries}/zkc.workspace.toml
  test -f ${sources.libraries}/libraries/core/polynomial/zkc.toml
  test ! -e ${sources.libraries}/crates
  test ! -e ${sources.application}/crates
  mkdir -p "$out"
''
