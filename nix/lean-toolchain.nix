{
  lib,
  stdenv,
  stdenvNoCC,
  fetchurl,
  zstd,
  autoPatchelfHook,
  makeWrapper,
  cc,
}:
let
  version = lib.removePrefix "leanprover/lean4:v" (
    lib.trim (builtins.readFile ../formal/lean-toolchain)
  );
  hashes = {
    "4.33.1" = "sha256:890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235";
  };
in
stdenvNoCC.mkDerivation {
  pname = "lean-toolchain";
  inherit version;
  src = fetchurl {
    url = "https://github.com/leanprover/lean4/releases/download/v${version}/lean-${version}-linux.tar.zst";
    hash = hashes.${version} or (throw "Add the upstream Linux asset hash for Lean ${version}");
  };
  nativeBuildInputs = [
    zstd
    autoPatchelfHook
    makeWrapper
  ];
  buildInputs = [ stdenv.cc.cc.lib ];
  installPhase = ''
    runHook preInstall
    mkdir -p "$out"
    cp -a . "$out/"
    runHook postInstall
  '';
  dontStrip = true;
  postFixup = ''
    # The upstream driver supports LEAN_CC. Its bundled libraries preserve the
    # release's C++ ABI; Nix's compiler wrapper selects a usable runtime loader.
    makeWrapper ${cc}/bin/clang "$out/bin/lean-cc" --add-flags "-L$out/lib"
    for tool in lean lake leanc; do
      wrapProgram "$out/bin/$tool" --set-default LEAN_CC "$out/bin/lean-cc"
    done
  '';
  meta = {
    description = "Exact upstream Lean/Lake toolchain selected by formal/lean-toolchain";
    license = lib.licenses.asl20;
    platforms = [ "x86_64-linux" ];
    mainProgram = "lean";
  };
}
