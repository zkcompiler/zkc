# Package inputs and check inputs have different cache boundaries.
{ lib }:
let
  source = import ./source.nix { inherit lib; };
  processSupport = [
    "scripts/processes.py"
    "scripts/reporting.py"
    "scripts/workspace.py"
  ];
  runner = processSupport ++ [ "common/tests/run.py" ];
  pytest = runner ++ [
    "pyproject.toml"
    "uv.lock"
    "common/tests/conftest.py"
    "common/tests/support"
  ];
  compiler = [
    "compiler/CMakeLists.txt"
    "compiler/cmake"
    "compiler/include"
    "compiler/lib"
    "compiler/tools"
    "common/unicode"
  ];
  rust = [
    "Cargo.toml"
    "Cargo.lock"
    "rust-toolchain.toml"
    "crates"
    "common/unicode"
  ];
  projects = [
    "examples"
    "libraries"
  ];
  rustFixtures = [
    "compiler/test/fixtures/relation/polynomial-chunks.json"
    "compiler/adapters/accumulator-machine/fixtures"
    "compiler/adapters/plonky3/fixtures/recurrence"
  ];
  lean = [
    "lean"
    "common/tests/fixtures/variants/history-contracts.txt"
    "common/tests/fixtures/blocks"
  ];
  definitions = {
    compiler.paths = compiler;
    compilerTests.paths =
      compiler
      ++ projects
      ++ processSupport
      ++ [
        "compiler/test"
        "compiler/CMakePresets.json"
        "compiler/examples/domain"
        "compiler/adapters/plonky3/fixtures/recurrence"
        "common/tests/support"
        "common/tests/fixtures/clean/air-control.json"
      ];
    compilerDomain.paths = compiler ++ [ "compiler/examples/domain" ];
    domainChecks.paths = processSupport ++ [
      "common/tests/check_domain.py"
      "compiler/examples/domain/consumer"
    ];
    consumer = {
      paths = [ "common/tests/consumer" ];
      exclude = [ "common/tests/consumer/test_discovery.py" ];
    };
    rust.paths = rust;
    rustTests.paths = rust ++ runner ++ rustFixtures ++ projects;
    application.paths = [
      "common/tests/check_install.py"
      "common/tests/support/project.py"
      "libraries/schnorr/lib.zkc"
      "examples/projects/schnorr"
      "examples/projects/mathematics/main.zkc"
      "libraries/zkc/vector.zkc"
      "libraries/zkc/symbolic.zkc"
    ];
    format.paths = [
      "scripts/format.py"
      ".clang-format"
      "compiler"
      "common/tests/consumer"
    ];
    sdk.paths = pytest ++ [
      "common/tests/consumer/test_discovery.py"
      "compiler/cmake"
    ];
    integration = {
      paths =
        pytest
        ++ rust
        ++ projects
        ++ [
          "common/tests/protocol"
          "common/tests/kernels"
          "common/tests/fixtures"
          "compiler/test"
          "compiler/include"
          "compiler/adapters/accumulator-machine"
          "compiler/adapters/plonky3/fixtures"
          "lean/integrations/clean/lake-manifest.json"
          "docs/getting-started.md"
          "docs/runtime/bundles.md"
        ];
      markdown = true;
    };
    lean = {
      paths = lean;
      exclude = [ "lean/integrations" ];
    };
    arklib.paths = [ "lean/integrations/arklib" ];
    leanChecks.paths =
      lean
      ++ runner
      ++ [
        "common/tests/support"
        "common/tests/fixtures/variants"
        "common/tests/fixtures/clean/air-control.json"
        "justfile"
        "examples/relations/multiply.r1cs.json"
      ];
    llzk.paths = [
      "compiler/adapters/llzk"
      "compiler/include/zkc/Support/MLIRInput.h"
    ];
    # Documentation, style and harness discovery inspect the repository itself.
    repository = {
      paths = builtins.attrNames (builtins.readDir ../.);
      markdown = true;
    };
  };
in
lib.mapAttrs (name: definition: source (definition // { inherit name; })) definitions
