{
  lib,
  stdenv,
  cmake,
  ninja,
  git,
  python3,
  llvm,
  source,
  fetchSource,
  nativeCompiler,
  pin ? (builtins.fromJSON (builtins.readFile ../compiler/adapters/llzk/pins.json)).llzk-current,
}:
let
  upstream = stdenv.mkDerivation {
    pname = "llzk";
    version = "${builtins.substring 0 12 pin.revision}";
    src = fetchSource pin.url pin.revision;
    nativeBuildInputs = [
      cmake
      ninja
      git
      python3
      llvm.tblgen
    ];
    buildInputs = [
      llvm.mlir
      llvm.llvm.dev
      llvm.libclang
    ];
    # Enable local degree-computation exceptions and support split LLVM headers.
    patches = [ ../compiler/adapters/llzk/toolchain.patch ];
    cmakeFlags = [
      # The pinned upstream nix/llzk.nix declares 3.0.0; shallow sources have no tags.
      "-DLLZK_VERSION_OVERRIDE=${pin.version}"
      "-DLLVM_DIR=${lib.getDev llvm.llvm}/lib/cmake/llvm"
      "-DMLIR_DIR=${lib.getDev llvm.mlir}/lib/cmake/mlir"
      "-DClang_DIR=${lib.getDev llvm.libclang}/lib/cmake/clang"
      "-DMLIR_TABLEGEN_EXE=${llvm.tblgen}/bin/mlir-tblgen"
      "-DLLVM_TABLEGEN_EXE=${llvm.tblgen}/bin/llvm-tblgen"
      "-DLLZK_WITH_PCL=OFF"
      "-DLLZK_ENABLE_BINDINGS_PYTHON=OFF"
      "-DLLZK_TBLGEN_USE_LIBCLANGCPP=ON"
      "-DBUILD_TESTING=OFF"
    ];
  };
in
stdenv.mkDerivation {
  pname = "zkc-llzk";
  version = "0.0.0";
  src = source;
  nativeBuildInputs = [
    cmake
    ninja
    python3
  ];
  buildInputs = [
    upstream
    llvm.mlir
    llvm.llvm.dev
  ];
  preConfigure = ''cmakeDir="$PWD/compiler/adapters/llzk"'';
  cmakeFlags = [
    "-DLLVM_DIR=${lib.getDev llvm.llvm}/lib/cmake/llvm"
    "-DMLIR_DIR=${lib.getDev llvm.mlir}/lib/cmake/mlir"
    "-DLLZK_DIR=${upstream}/lib/cmake/LLZK"
    "-DZKC_LLZK_REVISION=${pin.revision}"
    "-DZKC_NATIVE_COMPILER=${nativeCompiler}/bin/zkc-compile"
    "-DBUILD_TESTING=ON"
  ];
  doCheck = true;
  installPhase = ''
    mkdir -p "$out/bin" "$out/share/zkc-llzk"
    cp zkc-llzk "$out/bin/"
    cp ../compiler/adapters/llzk/pins.json "$out/share/zkc-llzk/"
  '';
  passthru = { inherit upstream; };
  meta = {
    description = "Isolated LLZK relation adapter with a pinned LLVM 23 toolchain";
    license = lib.licenses.asl20;
    platforms = [ "x86_64-linux" ];
    mainProgram = "zkc-llzk";
  };
}
