# Explicit CI acceptance: a writable cache mount is required for this probe.
{
  stdenv,
  ccache,
  python3,
}:
stdenv.mkDerivation {
  name = "zkc-compiler-cache-check";
  dontUnpack = true;
  dontConfigure = true;
  nativeBuildInputs = [
    ccache
    python3
  ];
  buildPhase = ''
    test -w /var/cache/zkc-ccache
    python3 ${./compiler-cache.py}
  '';
  installPhase = ''
    mkdir -p "$out"
    printf 'compiler cache invalidation controls passed\n' > "$out/result"
  '';
}
