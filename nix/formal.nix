{
  lib,
  stdenvNoCC,
  lean,
  git,
  python3,
  source,
  lakeSources,
}:
stdenvNoCC.mkDerivation {
  pname = "zkc-formal";
  version = "0.1.0";
  src = source;
  outputs = [
    "out"
    "library"
  ];
  nativeBuildInputs = [
    lean
    git
    python3
  ];
  dontConfigure = true;
  buildPhase = ''
    runHook preBuild
    cd formal
    # Tests.Variant embeds the shared inventory relative to its source file.
    test -f ../tests/fixtures/variants/history-contracts.txt
    mkdir -p .lake/packages
    for dependency in ${lakeSources}/*; do
      cp -R "$dependency/" ".lake/packages/$(basename "$dependency")"
    done
    chmod -R u+w .lake/packages
    # fetchgit omits the mutable index; restore it from the pinned commit.
    for dependency in .lake/packages/*; do
      git -C "$dependency" reset --mixed HEAD
    done
    export LEAN_NUM_THREADS="$NIX_BUILD_CORES"
    export MATHLIB_NO_CACHE_ON_UPDATE=1
    lake --no-cache build
    runHook postBuild
  '';
  installPhase = ''
    runHook preInstall
    mkdir -p "$library/share/zkc/formal" "$library/share/zkc/tests" "$out/bin"
    cp -a . "$library/share/zkc/formal/"
    cp -R ../tests/fixtures "$library/share/zkc/tests/fixtures"
    for executable in "$library/share/zkc/formal/.lake/build/bin/"*; do
      if [ -f "$executable" ] && [ -x "$executable" ]; then
        name=$(basename "$executable")
        mv "$executable" "$out/bin/$name"
        ln -s "$out/bin/$name" "$executable"
      fi
    done
    runHook postInstall
  '';
  # Lake traces hash native artifacts. Do not rewrite them after Lake builds.
  dontFixup = true;
  meta = {
    description = "Formal library, proofs, executable references, and independent checkers";
    license = lib.licenses.asl20;
    platforms = [ "x86_64-linux" ];
  };
}
