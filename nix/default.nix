{ inputs, system }:
let
  pkgs = import inputs.nixpkgs {
    inherit system;
    config = { };
    overlays = [ inputs.rust-overlay.overlays.default ];
  };
  inherit (pkgs) lib;
  llvm = pkgs.llvmPackages_23;
  rust = pkgs.rust-bin.fromRustupToolchainFile ../rust-toolchain.toml;
  rustDev = rust.override {
    extensions =
      (builtins.fromTOML (builtins.readFile ../rust-toolchain.toml)).toolchain.components
      ++ [ "rust-analyzer" ];
  };
  lean = pkgs.callPackage ./lean-toolchain.nix { cc = llvm.clang; };
  python = pkgs.python314;
  workspace = inputs.uv2nix.lib.workspace.loadWorkspace { workspaceRoot = ../.; };
  pythonSet =
    (pkgs.callPackage inputs.pyproject-nix.build.packages {
      inherit python;
    }).overrideScope
      (
        lib.composeManyExtensions [
          inputs.pyproject-build-systems.overlays.wheel
          (workspace.mkPyprojectOverlay { sourcePreference = "wheel"; })
        ]
      );
  pythonTools = pythonSet.mkVirtualEnv "zkc-python-tools" workspace.deps.all;
  environment = import ./environment.nix { inherit pkgs llvm python; };
  sourceFor = import ./source.nix { inherit lib; };
  # Native packages need shared test helpers, not checkout maintenance commands.
  nativeSupport = [
    "scripts/processes.py"
    "scripts/reporting.py"
    "scripts/workspace.py"
    "tests/support"
  ];
  compiler = pkgs.callPackage ./compiler.nix {
    inherit llvm;
    source = sourceFor "compiler" (
      nativeSupport
      ++ [
        "compiler"
        "examples"
        "libraries"
      ]
    );
    stdenv = llvm.stdenv;
    python3 = python;
  };
  compilerSanitize = compiler.overrideAttrs (old: {
    pname = "zkc-compiler-sanitize";
    doCheck = true;
    cmakeBuildType = "RelWithDebInfo";
    cmakeFlags = old.cmakeFlags ++ [
      "-DZKC_ENABLE_ASSERTIONS=ON"
      "-DZKC_ENABLE_SANITIZERS=ON"
    ];
    checkPhase = ''
      # Inline LLVM allocators are instrumented, but the release MLIR library
      # is not. Match the sanitizer preset; retain ordinary ASan/UBSan checks.
      export ASAN_OPTIONS="''${ASAN_OPTIONS:+$ASAN_OPTIONS:}allow_user_poisoning=0"
      ctest --output-on-failure --no-tests=error --parallel "$NIX_BUILD_CORES" -L native
    '';
  });
  # Optional installation checks build only the installed compiler graph.
  # Keep both linkage variants out of `checks` and the default package.
  domainCompiler =
    shared: envelope:
    compiler.overrideAttrs (old: {
      pname = "zkc-compiler-${if envelope then "envelope" else "base"}-${
        if shared then "shared" else "static"
      }";
      outputs = [ "out" ];
      doCheck = false;
      postInstall = "";
      cmakeFlags = old.cmakeFlags ++ [
        "-DBUILD_TESTING=OFF"
        "-DBUILD_SHARED_LIBS=${if shared then "ON" else "OFF"}"
      ];
      preConfigure =
        old.preConfigure
        + lib.optionalString envelope ''
          cmakeFlagsArray+=("-DZKC_CONTRIBUTION_FILES=$PWD/compiler/examples/domain/contribution.cmake")
        '';
      buildPhase = ''
        runHook preBuild
        cmake --build . --target zkc-compile zkc-opt zkc-tblgen --parallel "$NIX_BUILD_CORES"
        runHook postBuild
      '';
    });
  domainCheck =
    shared:
    pkgs.callPackage ./checks/compiler-domain.nix {
      inherit llvm shared;
      stdenv = llvm.stdenv;
      python3 = python;
      source = compiler.src;
      base = domainCompiler shared false;
      domain = domainCompiler shared true;
    };
  tools = pkgs.callPackage ./rust.nix {
    rustPlatform = pkgs.makeRustPlatform {
      cargo = rust;
      rustc = rust;
    };
    source = sourceFor "rust" (
      nativeSupport
      ++ [
        "Cargo.toml"
        "Cargo.lock"
        "rust-toolchain.toml"
        "crates"
        # Native relation tests consume the maintained compiler and adapter fixtures.
        "compiler/test/fixtures/relation/polynomial-chunks.json"
        "compiler/adapters/accumulator-machine/fixtures"
        "compiler/adapters/plonky3/fixtures/recurrence/bundle.json"
        "compiler/adapters/plonky3/fixtures/recurrence/bundle-configuration.json"
        "compiler/adapters/plonky3/fixtures/recurrence/bundle-instance.json"
        "compiler/adapters/plonky3/fixtures/recurrence/bundle-witness.json"
        "tests/run.py"
        "examples"
        "libraries"
      ]
    );
  };
  testDrivers = tools.overrideAttrs {
    pname = "zkc-test-drivers";
    cargoBuildFlags = [
      "-p"
      "zkc-test-drivers"
      "--bins"
    ];
    meta = {
      description = "Native integration test drivers";
      platforms = [ system ];
    };
  };
  testSupport = pkgs.symlinkJoin {
    name = "zkc-test-tools";
    paths = [
      tools
      testDrivers
    ];
  };
  zkc = pkgs.symlinkJoin {
    name = "zkc";
    paths = [ tools ];
    nativeBuildInputs = [ pkgs.makeWrapper ];
    postBuild = ''
      wrapProgram "$out/bin/zkc" --prefix PATH : "${compiler}/bin"
    '';
    meta = tools.meta // {
      description = "zkc compiler and execution CLI";
    };
  };
  lakeSourcesFor = pkgs.callPackage ./lake-sources.nix { };
  fetchSource = pkgs.callPackage ./external-source.nix { };
  llzk = pkgs.callPackage ./llzk.nix {
    inherit fetchSource;
    llvm = pkgs.llvmPackages_20;
    stdenv = pkgs.llvmPackages_20.stdenv;
    python3 = python;
    source = sourceFor "llzk" [
      "compiler/adapters/llzk"
      "compiler/include/zkc/Support/MLIRInput.h"
    ];
  };
  lakeSources = lakeSourcesFor ../formal/lake-manifest.json;
  formal = pkgs.callPackage ./formal.nix {
    inherit lean lakeSources;
    python3 = python;
    source = sourceFor "formal" [
      "formal"
      "tests/fixtures/variants/history-contracts.txt"
      "tests/fixtures/blocks"
    ];
  };
  arklib =
    assert
      lib.trim (builtins.readFile ../formal/lean-toolchain)
      == lib.trim (builtins.readFile ../formal/integrations/arklib/lean-toolchain);
    pkgs.callPackage ./arklib.nix {
      inherit formal lean;
      source = sourceFor "arklib" [ "formal" ];
      python3 = python;
      lakeSources = lakeSourcesFor ../formal/integrations/arklib/lake-manifest.json;
    };
  checkSource = sourceFor "checks" (builtins.attrNames (builtins.readDir ../.));
in
{
  packages = {
    inherit
      compiler
      tools
      zkc
      formal
      arklib
      llzk
      ;
    lake-sources = lakeSources;
    default = zkc;
    test-drivers = testDrivers;
    lean-toolchain = lean;
    rust-toolchain = rust;
    python-tools = pythonTools;
    compiler-sanitize = compilerSanitize;
    compiler-domain-checks = domainCheck false;
    compiler-domain-shared-checks = domainCheck true;
    formal-checks = pkgs.callPackage ./checks/formal.nix {
      inherit formal lean environment;
      source = checkSource;
      python3 = python;
    };
    lean-toolchain-checks = pkgs.callPackage ./checks/lean-toolchain.nix { inherit lean; };
  };
  checks = {
    compiler = compiler.overrideAttrs { doCheck = true; };
    application = pkgs.callPackage ./checks/application.nix {
      inherit zkc compiler;
      source = checkSource;
      python3 = python;
    };
    format = pkgs.callPackage ./checks/format.nix {
      source = checkSource;
      clang-tools = llvm.clang-tools;
      python3 = python;
    };
    sandbox = pkgs.callPackage ./checks/sandbox.nix { python3 = python; };
    git-source = pkgs.callPackage ./checks/git-source.nix { };
    style = pkgs.callPackage ./checks/style.nix {
      inherit pythonTools;
      python3 = python;
      source = checkSource;
    };
    compiler-consumer = pkgs.callPackage ./checks/compiler-consumer.nix {
      inherit compiler llvm;
      stdenv = llvm.stdenv;
    };
    project = pkgs.callPackage ./checks/project.nix {
      inherit
        pythonTools
        environment
        compiler
        tools
        testSupport
        ;
      source = checkSource;
      python3 = python;
    };
    rust = pkgs.callPackage ./checks/rust.nix {
      inherit tools environment;
      python3 = python;
    };
  };
  formatter = pkgs.writeShellApplication {
    name = "zkc-nixfmt";
    runtimeInputs = [ pkgs.nixfmt ];
    text = ''exec nixfmt "$@" flake.nix nix/*.nix nix/checks/*.nix'';
  };
  devShells.maintenance = pkgs.mkShell {
    packages = [
      python
      pkgs.nix-prefetch-git
      pkgs.git
    ];
  };
  # Source-only validation must not realize LLVM, MLIR or the Lean toolchain.
  devShells.quick = pkgs.mkShellNoCC {
    packages = [
      python
      rust
      pkgs.uv
      pkgs.just
      pkgs.actionlint
      pkgs.nixfmt
    ];
    UV_PYTHON = python.interpreter;
    UV_PYTHON_DOWNLOADS = "never";
  };
  devShells.formal = pkgs.mkShellNoCC {
    packages = [
      lean
      python
      pkgs.git
      pkgs.just
    ];
    LEAN_NUM_THREADS = "4";
  };
  devShells.default = import ./shell.nix {
    inherit
      pkgs
      llvm
      python
      environment
      ;
    rust = rustDev;
  };
}
