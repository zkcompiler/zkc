{
  lib,
  stdenv,
  cmake,
  ninja,
  python3,
  pkg-config,
  llvm,
  fetchurl,
  or-tools,
  source,
}:
let
  pins = builtins.fromJSON (builtins.readFile ../compiler/external/heir/pins.json);
  upstream = fetchurl {
    url = pins.heir.url;
    sha256 = pins.heir.sha256;
  };
  # The upstream CMake package discovers these even for a C++ consumer. Reuse
  # its exact Abseil/Protobuf/Re2 builds, rather than introducing another ABI.
  dependencyNames = [
    "abseil-cpp"
    "protobuf"
    "bzip2"
    "cbc"
    "clp"
    "cgl"
    "osi"
    "coinutils"
    "blas"
    "eigen"
    "glpk"
    "highs"
    "re2"
    "zlib"
    "scipopt-scip"
  ];
  select =
    dependencies:
    builtins.filter (
      dependency: !(dependency ? pythonModule) && builtins.elem (lib.getName dependency) dependencyNames
    ) dependencies;
  entry = dependency: {
    key = toString dependency;
    value = dependency;
  };
  cppDependencies = map (item: item.value) (
    builtins.genericClosure {
      startSet = map entry (select (or-tools.buildInputs ++ or-tools.propagatedBuildInputs));
      operator = item: map entry (select (item.value.buildInputs ++ item.value.propagatedBuildInputs));
    }
  );
in
assert
  builtins.hashFile "sha256" ../compiler/external/heir/patches/arithmetic.patch
  == (builtins.head pins.patches).sha256;
assert or-tools.version == lib.removePrefix "v" pins.ortools.release;
assert or-tools.src.outputHash == pins.ortools.source_hash;
stdenv.mkDerivation {
  pname = "zkc-heir-arithmetic";
  version = lib.removePrefix "v" pins.heir.version;
  src = source;
  nativeBuildInputs = [
    cmake
    ninja
    python3
    llvm.tblgen
  ];
  propagatedNativeBuildInputs = [ pkg-config ];
  propagatedBuildInputs = [
    llvm.mlir
    llvm.llvm.dev
    or-tools
  ]
  ++ cppDependencies;
  postUnpack = ''
    mkdir -p "$sourceRoot/upstream"
    tar -xf ${upstream} --strip-components=1 -C "$sourceRoot/upstream"
  '';
  postPatch = ''
    cd upstream
    patch --batch --fuzz=0 -p1 < ../compiler/external/heir/patches/arithmetic.patch
    cd ..
  '';
  preConfigure = ''
    cmakeDir="$PWD/compiler/external/heir"
    cmakeFlagsArray+=("-DZKC_HEIR_SOURCE_DIR=$PWD/upstream")
  '';
  cmakeFlags = [
    "-DPython3_EXECUTABLE=${python3.interpreter}"
    "-DLLVM_DIR=${lib.getDev llvm.llvm}/lib/cmake/llvm"
    "-DMLIR_DIR=${lib.getDev llvm.mlir}/lib/cmake/mlir"
    "-DMLIR_TABLEGEN_EXE=${llvm.tblgen}/bin/mlir-tblgen"
    "-DBUILD_TESTING=ON"
  ];
  doCheck = true;
  meta = {
    description = "Qualified HEIR arithmetic dialects, transformations and readers";
    license = lib.licenses.asl20;
    platforms = [ "x86_64-linux" ];
  };
}
