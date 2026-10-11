{
  pkgs,
  llvm,
  rust,
  python,
  environment,
  utf8proc,
}:
pkgs.mkShell.override { stdenv = llvm.stdenv; } (
  environment.toolchain
  // {
    packages = [
      llvm.mlir
      llvm.llvm.dev
      llvm.tblgen
      llvm.clang-tools
      utf8proc
      pkgs.cmake
      pkgs.ninja
      pkgs.ccache
      pkgs.just
      pkgs.git
      pkgs.pkg-config
      rust
      python
      pkgs.uv
      pkgs.actionlint
      pkgs.nixfmt
    ];
    shellHook = environment.development + ''
      # This is a local incremental-build cache, not an input to Nix packages.
      export CMAKE_C_COMPILER_LAUNCHER="''${CMAKE_C_COMPILER_LAUNCHER-ccache}"
      export CMAKE_CXX_COMPILER_LAUNCHER="''${CMAKE_CXX_COMPILER_LAUNCHER-ccache}"
      export CCACHE_BASEDIR="''${CCACHE_BASEDIR-$PWD}"
      export CCACHE_NAMESPACE="''${CCACHE_NAMESPACE-zkc-${llvm.clang}}"
      # Select the compiler matching the main MLIR package explicitly.
      export PATH="${llvm.clang}/bin:$PATH"
      if [ -z "''${TZ+x}" ] && [ ! -r /etc/localtime ]; then export TZ=UTC; fi
    '';
  }
)
