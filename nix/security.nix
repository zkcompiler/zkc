{
  lib,
  stdenvNoCC,
  lean,
  source,
  leanToolchain,
  git,
  python3,
  lakeSources,
}:
stdenvNoCC.mkDerivation {
  pname = "zkc-security";
  version = "0.0.0";
  dontUnpack = true;
  dontConfigure = true;
  nativeBuildInputs = [
    leanToolchain
    git
    python3
  ];
  buildPhase = ''
    cp -R ${lean.library}/share/zkc/lean lean
    chmod -R u+w lean
    cp -R ${source}/lean/. lean/
    chmod -R u+w lean
    cd lean
    mkdir -p security/.lake/packages
    for dependency in ${lakeSources}/*; do
      name=$(basename "$dependency")
      if [ -d ".lake/packages/$name" ]; then
        ln -s "$PWD/.lake/packages/$name" "security/.lake/packages/$name"
      else
        cp -R "$dependency/" "security/.lake/packages/$name"
        chmod -R u+w "security/.lake/packages/$name"
        git -C "security/.lake/packages/$name" reset --mixed HEAD
      fi
    done
    # Apply a declared dependency patch, if any, to its exact pinned revision.
    python3 -c 'from pathlib import Path; from support.compatibility import prepare; prepare(Path("security").resolve())'
    export LEAN_NUM_THREADS="$NIX_BUILD_CORES"
    export MATHLIB_NO_CACHE_ON_UPDATE=1
    (cd security && lake --no-cache build)
  '';
  doCheck = true;
  checkPhase = ''
    python3 checks/check_library.py --integration security
    python3 checks/check_package_ownership.py --integration security
    python3 checks/audit_imports.py --integration security
    python3 checks/check_clients.py --with-security --output "$TMPDIR/clients-security"
  '';
  installPhase = ''
    mkdir -p "$out/share/zkc/lean" "$out/share/zkc/common/tests" "$out/reports"
    # Replace temporary absolute links before publishing the package.
    for dependency in security/.lake/packages/*; do
      if [ -L "$dependency" ]; then
        name=$(basename "$dependency")
        rm "$dependency"
        ln -s "../../../.lake/packages/$name" "$dependency"
      fi
    done
    cp -a . "$out/share/zkc/lean/"
    # Logs and source records remain useful; temporary dependency links do not.
    (cd "$TMPDIR/clients-security" &&
      find . -type f ! -path '*/.lake/*' -exec cp --parents {} "$out/reports/" \;)
  '';
  dontFixup = true;
  meta = {
    description = "Reusable ArkLib-free security library and standalone consumer audits";
    license = lib.licenses.asl20;
    platforms = [ "x86_64-linux" ];
  };
}
