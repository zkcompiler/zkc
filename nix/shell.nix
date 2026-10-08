{
  pkgs,
  llvm,
  rust,
  python,
  environment,
}:
pkgs.mkShell.override { stdenv = llvm.stdenv; } (
  environment.toolchain
  // {
    packages = [
      llvm.mlir
      llvm.llvm.dev
      llvm.tblgen
      llvm.clang-tools
      pkgs.cmake
      pkgs.ninja
      pkgs.just
      pkgs.git
      pkgs.pkg-config
      rust
      python
      pkgs.uv
      pkgs.nixfmt
    ];
    shellHook = environment.development + ''
      # Select the compiler matching the main MLIR package explicitly.
      export PATH="${llvm.clang}/bin:$PATH"
      if [ -z "''${TZ+x}" ] && [ ! -r /etc/localtime ]; then export TZ=UTC; fi
    '';
  }
)
