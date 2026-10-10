# Guard meaningful package/check boundaries using the actual filtered trees.
{ runCommandNoCC, sources }:
runCommandNoCC "zkc-source-boundaries" { } ''
  set -x
  test -f ${sources.compiler}/compiler/CMakeLists.txt
  test -f ${sources.compiler}/common/unicode/generate.py
  test ! -e ${sources.compiler}/compiler/test
  test ! -e ${sources.compiler}/common/tests
  test ! -e ${sources.compiler}/lean
  test -f ${sources.compilerTests}/common/tests/fixtures/clean/air-control.json
  test -f ${sources.compilerTests}/compiler/test/CMakeLists.txt
  test ! -e ${sources.compilerTests}/common/tests/run.py
  test -f ${sources.rust}/crates/zkc-tools/Cargo.toml
  test ! -e ${sources.rust}/scripts
  test ! -e ${sources.rust}/compiler
  test ! -e ${sources.rust}/common/tests
  test -f ${sources.rustTests}/compiler/test/fixtures/relation/polynomial-chunks.json
  test ! -e ${sources.integration}/common/tests/harness
  test ! -e ${sources.integration}/common/tests/consumer
  test -f ${sources.integration}/docs/getting-started.md
  test -f ${sources.sdk}/common/tests/consumer/test_discovery.py
  test ! -e ${sources.sdk}/compiler/lib
  test ! -e ${sources.lean}/lean/integrations
  test -f ${sources.leanChecks}/common/tests/fixtures/clean/air-control.json
  test ! -e ${sources.arklib}/lean/integrations/clean
  test ! -e ${sources.application}/crates
  mkdir -p "$out"
''
