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
  compiler = pkgs.callPackage ./compiler.nix {
    inherit llvm;
    source = sourceFor "compiler" [
      "scripts"
      "compiler"
      "tests/support"
      "tests/fixtures"
      "examples"
      "bench/protocol_experiment.py"
    ];
    stdenv = llvm.stdenv;
    python3 = python;
  };
  compilerSanitize = compiler.overrideAttrs (old: {
    pname = "zkc-compiler-sanitize";
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
  tools = pkgs.callPackage ./rust.nix {
    rustPlatform = pkgs.makeRustPlatform {
      cargo = rust;
      rustc = rust;
    };
    source = sourceFor "rust" [
      "scripts"
      "Cargo.toml"
      "Cargo.lock"
      "rust-toolchain.toml"
      "crates"
      "tests/run.py"
      "tests/support"
      "tests/groth16"
      "examples"
      "tests/fixtures"
    ];
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
  groth16 = pkgs.callPackage ./groth16.nix {
    inherit fetchSource;
    llvm = pkgs.llvmPackages_20;
    llzk =
      (llzk.override {
        pin =
          (builtins.fromJSON (builtins.readFile ../compiler/adapters/llzk/pins.json)).llzk-circom-locked;
        withPcl = true;
      }).upstream;
    rustPlatform = pkgs.makeRustPlatform {
      cargo = rust;
      rustc = rust;
    };
    nodejs = pkgs.nodejs_26;
    python3 = python;
    source = sourceFor "groth16" [ "tests/groth16" ];
  };
  lakeSources = lakeSourcesFor ../formal/lake-manifest.json;
  formal = pkgs.callPackage ./formal.nix {
    inherit lean lakeSources;
    python3 = python;
    source = sourceFor "formal" [
      "formal"
      "tests/fixtures/variants/history-contracts.txt"
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
      formal
      arklib
      llzk
      groth16
      ;
    lake-sources = lakeSources;
    default = compiler;
    lean-toolchain = lean;
    rust-toolchain = rust;
    python-tools = pythonTools;
    compiler-sanitize = compilerSanitize;
    groth16-checks = pkgs.callPackage ./checks/groth16.nix {
      inherit
        compiler
        tools
        formal
        groth16
        environment
        ;
      nodejs = pkgs.nodejs_26;
      python3 = python;
    };
  };
  checks = {
    inherit compiler;
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
    lean-toolchain = pkgs.callPackage ./checks/lean-toolchain.nix { inherit lean; };
    project = pkgs.callPackage ./checks/project.nix {
      inherit
        pythonTools
        environment
        lean
        compiler
        tools
        formal
        ;
      source = checkSource;
      python3 = python;
    };
    rust = pkgs.callPackage ./checks/rust.nix {
      inherit
        compiler
        tools
        formal
        environment
        ;
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
  devShells.default = import ./shell.nix {
    inherit
      pkgs
      llvm
      lean
      python
      environment
      ;
    rust = rustDev;
  };
}
