{
  lib,
  stdenv,
  fetchurl,
  cmake,
  ninja,
}:
let
  pin = (builtins.fromJSON (builtins.readFile ../common/unicode/manifest.json)).normalizers.cpp;
in
stdenv.mkDerivation {
  pname = "utf8proc";
  inherit (pin) version;
  src = fetchurl {
    name = "utf8proc-${pin.version}.tar.gz";
    inherit (pin) url sha256;
  };
  nativeBuildInputs = [
    cmake
    ninja
  ];
  cmakeFlags = [
    "-DBUILD_SHARED_LIBS=ON"
    # Upstream tests fetch Unicode 18 data during configure. zkc exercises the
    # pinned, vendored Unicode 17 corpus independently and without networking.
    "-DUTF8PROC_ENABLE_TESTING=OFF"
  ];
  meta = {
    description = "Pinned NFC implementation for zkc source names";
    homepage = "https://github.com/JuliaStrings/utf8proc";
    license = lib.licenses.mit;
    platforms = lib.platforms.all;
  };
}
