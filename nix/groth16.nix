{
  lib,
  stdenvNoCC,
  rustPlatform,
  fetchSource,
  fetchNpmDeps,
  nodejs,
  python3,
  git,
  symlinkJoin,
  llvm,
  llzk,
  source,
  libxml2,
  zlib,
}:
let
  pins = builtins.fromJSON (builtins.readFile ../tests/groth16/SOURCE_PINS.json);
  circomSource = fetchSource pins.circom.repository pins.circom.commit;
  circomlib = fetchSource pins.circomlib.repository pins.circomlib.commit;
  # mlir-sys asks llvm-config for one prefix containing both LLVM and MLIR.
  # Nix keeps those libraries in separate outputs; supply the expected view.
  llvmPrefix = symlinkJoin {
    name = "llvm-mlir-20-circom-prefix";
    paths = [
      llvm.mlir.dev
      llvm.mlir
      llvm.llvm.dev
      llvm.llvm
      llvm.llvm.lib
    ];
    postBuild = ''
      rm "$out/bin/llvm-config"
      cat > "$out/bin/llvm-config" <<EOF
      #!${stdenvNoCC.shell}
      case "\$*" in
        *--libdir*) printf '%s\\n' '$out/lib' ;;
        *--includedir*) printf '%s\\n' '$out/include' ;;
        *) exec ${llvm.llvm.dev}/bin/llvm-config "\$@" ;;
      esac
      EOF
      chmod +x "$out/bin/llvm-config"
    '';
  };
  circom = rustPlatform.buildRustPackage {
    pname = "circom";
    version = pins.circom.version;
    src = circomSource;
    cargoHash = "sha256-N/ssbunZELot+wjsy4ilqQN3tF4CwwCfZ4nPjr3nNNY=";
    nativeBuildInputs = [ rustPlatform.bindgenHook ];
    buildInputs = [
      llvm.mlir
      llvm.llvm.dev
      llzk
      libxml2
      zlib
    ];
    LIBCLANG_PATH = "${llvm.libclang.lib}/lib";
    MLIR_SYS_200_PREFIX = llvmPrefix;
    TABLEGEN_200_PREFIX = llvmPrefix;
    LLZK_SYS_10_PREFIX = llzk;
    # tblgen's build dependency compiles C++ with -Werror. Optimize that code
    # too, as required by the stdenv's enabled _FORTIFY_SOURCE hardening.
    CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL = "2";
    doCheck = false;
  };
  npmCache = fetchNpmDeps {
    src = ../tests/groth16;
    hash = "sha256-zyUpnN4ihveHNtcXAfDLBgtZc14UsoUS6l4Tp8G+BqE=";
  };
in
stdenvNoCC.mkDerivation {
  pname = "zkc-groth16-fixtures";
  version = "0.1.0";
  src = source;
  nativeBuildInputs = [
    nodejs
    python3
    git
  ];
  dontConfigure = true;
  buildPhase = ''
    runHook preBuild
    for name in circom circomlib; do
      if [ "$name" = circom ]; then dep=${circomSource}; else dep=${circomlib}; fi
      cp -R "$dep" "$TMPDIR/$name"
      chmod -R u+w "$TMPDIR/$name"
      git -C "$TMPDIR/$name" reset --mixed HEAD
    done
    cp -R ${npmCache} "$TMPDIR/npm-cache"
    chmod -R u+w "$TMPDIR/npm-cache"
    python3 tests/groth16/reproduce.py all --offline --workers "$NIX_BUILD_CORES" \
      --circom ${circom}/bin/circom --circom-source "$TMPDIR/circom" \
      --circomlib-source "$TMPDIR/circomlib" --npm-cache "$TMPDIR/npm-cache" \
      --workdir "$TMPDIR/fixture"
    runHook postBuild
  '';
  installPhase = ''
    mkdir -p "$out"
    cp -R "$TMPDIR/fixture/." "$out/"
  '';
  dontFixup = true;
  passthru = { inherit circom npmCache; };
  meta = {
    description = "Reproduced Groth16 fixtures with public deterministic test setup";
    license = lib.licenses.asl20;
    platforms = [ "x86_64-linux" ];
  };
}
