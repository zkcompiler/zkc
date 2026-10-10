{ inputs, system }:
let
  pkgs = import inputs.nixpkgs {
    inherit system;
    config = { };
    overlays = [ inputs.rust-overlay.overlays.default ];
  };
  inherit (pkgs) lib;
  llvm = pkgs.llvmPackages_23;
  utf8proc = pkgs.callPackage ./utf8proc.nix { stdenv = llvm.stdenv; };
  rust = pkgs.rust-bin.fromRustupToolchainFile ../rust-toolchain.toml;
  rustDev = rust.override {
    extensions =
      (builtins.fromTOML (builtins.readFile ../rust-toolchain.toml)).toolchain.components
      ++ [ "rust-analyzer" ];
  };
  leanToolchain = pkgs.callPackage ./lean-toolchain.nix { cc = llvm.clang; };
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
  sources = import ./sources.nix { inherit lib; };
  compiler = pkgs.callPackage ./compiler.nix {
    inherit llvm utf8proc;
    source = sources.compiler;
    stdenv = llvm.stdenv;
    python3 = python;
  };
  compilerChecks = compiler.override {
    withTests = true;
    source = sources.compilerTests;
  };
  compilerSanitize = compilerChecks.overrideAttrs (old: {
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
  # Optional installation checks build only the installed compiler graph.
  # Keep both linkage variants out of `checks` and the default package.
  domainCompiler =
    shared: envelope:
    if !shared && !envelope then
      compiler
    else
      (compiler.override { source = if envelope then sources.compilerDomain else sources.compiler; })
      .overrideAttrs
        (old: {
          pname = "zkc-compiler-${if envelope then "envelope" else "base"}-${
            if shared then "shared" else "static"
          }";
          cmakeFlags = old.cmakeFlags ++ [
            "-DBUILD_SHARED_LIBS=${if shared then "ON" else "OFF"}"
          ];
          preConfigure =
            old.preConfigure
            + lib.optionalString envelope ''
              cmakeFlagsArray+=("-DZKC_CONTRIBUTION_FILES=$PWD/compiler/examples/domain/contribution.cmake")
            '';
        });
  domainCheck =
    shared:
    pkgs.callPackage ./checks/compiler-domain.nix {
      inherit llvm shared utf8proc;
      stdenv = llvm.stdenv;
      python3 = python;
      source = sources.domainChecks;
      base = domainCompiler shared false;
      domain = domainCompiler shared true;
    };
  tools = pkgs.callPackage ./rust.nix {
    rustPlatform = pkgs.makeRustPlatform {
      cargo = rust;
      rustc = rust;
    };
    source = sources.rust;
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
    source = sources.llzk;
  };
  lakeSources = lakeSourcesFor ../lean/lake-manifest.json;
  lean = pkgs.callPackage ./lean.nix {
    inherit leanToolchain lakeSources;
    python3 = python;
    source = sources.lean;
  };
  arklib =
    assert
      lib.trim (builtins.readFile ../lean/lean-toolchain)
      == lib.trim (builtins.readFile ../lean/integrations/arklib/lean-toolchain);
    pkgs.callPackage ./arklib.nix {
      inherit lean leanToolchain;
      source = sources.arklib;
      python3 = python;
      lakeSources = lakeSourcesFor ../lean/integrations/arklib/lake-manifest.json;
    };
in
{
  packages = {
    inherit
      compiler
      tools
      zkc
      lean
      arklib
      llzk
      ;
    lake-sources = lakeSources;
    default = zkc;
    test-drivers = testDrivers;
    lean-toolchain = leanToolchain;
    rust-toolchain = rust;
    python-tools = pythonTools;
    compiler-sanitize = compilerSanitize;
    compiler-domain-checks = domainCheck false;
    compiler-domain-shared-checks = domainCheck true;
    lean-checks = pkgs.callPackage ./checks/lean.nix {
      inherit lean leanToolchain environment;
      source = sources.leanChecks;
      python3 = python;
    };
    lean-toolchain-checks = pkgs.callPackage ./checks/lean-toolchain.nix { inherit leanToolchain; };
  };
  checks = {
    sources = pkgs.callPackage ./checks/sources.nix { inherit sources; };
    harness = pkgs.callPackage ./checks/python.nix {
      inherit pythonTools environment;
      python3 = python;
      source = sources.repository;
      scope = "harness";
    };
    sdk = pkgs.callPackage ./checks/python.nix {
      inherit pythonTools environment;
      python3 = python;
      source = sources.sdk;
      scope = "sdk";
    };
    compiler = compilerChecks;
    application = pkgs.callPackage ./checks/application.nix {
      inherit zkc compiler;
      source = sources.application;
      python3 = python;
    };
    format = pkgs.callPackage ./checks/format.nix {
      source = sources.format;
      clang-tools = llvm.clang-tools;
      python3 = python;
    };
    sandbox = pkgs.callPackage ./checks/sandbox.nix { python3 = python; };
    git-source = pkgs.callPackage ./checks/git-source.nix { };
    style = pkgs.callPackage ./checks/style.nix {
      inherit pythonTools rust;
      python3 = python;
      source = sources.repository;
    };
    compiler-consumer = pkgs.callPackage ./checks/compiler-consumer.nix {
      inherit compiler llvm;
      source = sources.consumer;
      stdenv = llvm.stdenv;
    };
    project = pkgs.callPackage ./checks/project.nix {
      inherit
        pythonTools
        environment
        tools
        testSupport
        ;
      compiler = compilerChecks;
      source = sources.integration;
      python3 = python;
    };
    rust = pkgs.callPackage ./checks/rust.nix {
      inherit tools environment;
      source = sources.rustTests;
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
  devShells.lean = pkgs.mkShellNoCC {
    packages = [
      leanToolchain
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
      utf8proc
      ;
    rust = rustDev;
  };
}
