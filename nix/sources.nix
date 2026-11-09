# Package inputs and check inputs have different cache boundaries.
{ lib }:
let
  source = import ./source.nix { inherit lib; };
  processSupport = [
    "scripts/processes.py"
    "scripts/reporting.py"
    "scripts/workspace.py"
  ];
  runner = processSupport ++ [
    "common/tests/run.py"
    "common/tests/smoke.py"
    "common/tests/smoke.json"
  ];
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
    "common/catalog"
    "common/targets"
  ];
  rust = [
    "Cargo.toml"
    "Cargo.lock"
    "rust-toolchain.toml"
    "crates"
    "common/unicode"
    "common/catalog/declarations.json"
    "common/catalog/installation.json"
    "common/catalog/validation-cases.json"
    "common/targets/evm.json"
    "common/targets/evm-validation-cases.json"
  ];
  projects = [
    "zkc.workspace.toml"
    "examples"
    "libraries"
    "common/tests/fixtures/projects"
  ];
  rustFixtures = [
    "common/tests/fixtures/program/bytes.json"
    "common/tests/fixtures/entry-json/nodes.json"
    "compiler/test/fixtures/relation/polynomial-chunks.json"
    "compiler/test/fixtures/common-inputs/custody-fields.json"
    "compiler/adapters/accumulator-machine/fixtures"
    "compiler/adapters/plonky3/fixtures/recurrence"
  ];
  leanInventory = import ./lean-packages.nix { inherit lib; };
  formal = lib.mapAttrs' (
    name: entry:
    lib.nameValuePair "lean-${name}" {
      paths = [
        entry.relative
        "lean/checks"
        "lean/support"
        "lean/clients"
        "lean/lean-toolchain"
        "lean/bridges/common/lean_render.py"
      ];
    }
  ) leanInventory;
  definitions = {
    compiler.paths = compiler;
    compilerTests.paths =
      compiler
      ++ projects
      ++ processSupport
      ++ [
        "compiler/test"
        "lean/bridges/common/fixtures/schnorr-forms.zkc"
        "compiler/CMakePresets.json"
        "compiler/examples/domain"
        "compiler/adapters/plonky3/fixtures/recurrence"
        "common/tests/support"
        "common/tests/fixtures/clean/air-control.json"
        "common/tests/fixtures/program/bytes.json"
        "common/tests/fixtures/entry-json/nodes.json"
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
    # Crate documentation can be a compilation input through include_str!.
    rustConsumer = {
      paths = rust ++ [
        "common/tests/check_rust_sdk.py"
        "common/tests/consumer/rust"
      ];
      markdown = true;
    };
    rust = {
      paths = rust;
      markdown = true;
    };
    rustTests = {
      paths = rust ++ runner ++ rustFixtures ++ projects;
      markdown = true;
    };
    application.paths = [
      "zkc.workspace.toml"
      "common/tests/check_install.py"
      "common/tests/support/project.py"
      "libraries"
      "examples/projects/schnorr"
      "common/tests/fixtures/projects/mathematics"
    ];
    libraries.paths = [
      "zkc.workspace.toml"
      "libraries"
    ];
    format.paths = [
      "scripts/format.py"
      ".clang-format"
      "compiler"
      "common/tests/consumer"
      "common/benchmarks/monero.cpp"
    ];
    sdk.paths = pytest ++ [
      "common/tests/check_sdk.py"
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
          "compiler/adapters/clean"
          "compiler/adapters/ring_arena.py"
          "compiler/adapters/plonky3/fixtures"
          "lean/adapters/clean/lake-manifest.json"
          "docs/getting-started.md"
          "docs/runtime/bundles.md"
        ];
      markdown = true;
    };
    leanChecks.paths = [
      "lean"
    ]
    ++ runner
    ++ [
      "common/tests/support"
      "common/tests/fixtures/clean/air-control.json"
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
  }
  // formal;
in
lib.mapAttrs (name: definition: source (definition // { inherit name; })) definitions
