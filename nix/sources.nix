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
  ];
  rust = [
    "Cargo.toml"
    "Cargo.lock"
    "rust-toolchain.toml"
    "crates"
    "common/unicode"
    "common/catalog/declarations.json"
  ];
  projects = [
    "zkc.workspace.toml"
    "examples"
    "libraries"
    "common/tests/fixtures/projects"
  ];
  rustFixtures = [
    "common/tests/fixtures/program/bytes.json"
    "compiler/test/fixtures/relation/polynomial-chunks.json"
    "compiler/adapters/accumulator-machine/fixtures"
    "compiler/adapters/plonky3/fixtures/recurrence"
  ];
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
          "lean/integrations/clean/lake-manifest.json"
          "docs/getting-started.md"
          "docs/runtime/bundles.md"
        ];
      markdown = true;
    };
    lean.paths = [
      "lean/lakefile.toml"
      "lean/lake-manifest.json"
      "lean/lean-toolchain"
      "lean/Zkc.lean"
      "lean/Zkc"
      "lean/Tests"
      "lean/ZkcExamples"
      "lean/ZkcTools"
      "lean/checks/DeclarationRecords.lean"
    ];
    security.paths = [
      "lean/security"
      "lean/checks/check_clients.py"
      "lean/clients"
      "lean/support/lake.py"
      "lean/support/evidence.py"
      "lean/support/compatibility.py"
      "lean/support/packages.py"
      "lean/support/dependencies.py"
      "lean/support/lean_headers.py"
      "lean/checks/check_library.py"
      "lean/checks/check_package_ownership.py"
      "lean/checks/audit_imports.py"
    ];
    arklib.paths = [
      "lean/integrations/arklib"
      "lean/checks/check_clients.py"
      "lean/clients"
      "lean/support/lake.py"
      "lean/support/evidence.py"
      "lean/support/compatibility.py"
      "lean/support/packages.py"
      "lean/support/dependencies.py"
      "lean/support/lean_headers.py"
      "lean/checks/check_library.py"
      "lean/checks/check_package_ownership.py"
      "lean/checks/audit_imports.py"
    ];
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
  };
in
lib.mapAttrs (name: definition: source (definition // { inherit name; })) definitions
