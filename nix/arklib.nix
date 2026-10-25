{
  lib,
  stdenvNoCC,
  security,
  source,
  leanToolchain,
  git,
  python3,
  lakeSources,
}:
stdenvNoCC.mkDerivation {
  pname = "zkc-arklib";
  version = "0.0.0";
  dontUnpack = true;
  dontConfigure = true;
  nativeBuildInputs = [
    leanToolchain
    git
    python3
  ];
  buildPhase = ''
    cp -R ${security}/share/zkc/lean lean
    chmod -R u+w lean
    cp -R ${source}/lean/. lean/
    chmod -R u+w lean
    cd lean
    mkdir -p integrations/arklib/.lake/packages
    for dependency in ${lakeSources}/*; do
      name=$(basename "$dependency")
      if [ -d "security/.lake/packages/$name" ]; then
        ln -s "$PWD/security/.lake/packages/$name" "integrations/arklib/.lake/packages/$name"
      elif [ -d ".lake/packages/$name" ]; then
        ln -s "$PWD/.lake/packages/$name" "integrations/arklib/.lake/packages/$name"
      else
        cp -R "$dependency/" "integrations/arklib/.lake/packages/$name"
        chmod -R u+w "integrations/arklib/.lake/packages/$name"
        git -C "integrations/arklib/.lake/packages/$name" reset --mixed HEAD
      fi
    done
    # Apply a declared dependency patch, if any, to its exact pinned revision.
    python3 -c 'from pathlib import Path; from support.compatibility import prepare; prepare(Path("integrations/arklib").resolve())'
    export LEAN_NUM_THREADS="$NIX_BUILD_CORES"
    export MATHLIB_NO_CACHE_ON_UPDATE=1
    (cd integrations/arklib && lake --no-cache build)
  '';
  doCheck = true;
  checkPhase = ''
    python3 checks/check_library.py --integration arklib
    python3 checks/check_package_ownership.py --integration arklib
    python3 checks/audit_imports.py --integration arklib
    python3 checks/check_clients.py --with-arklib --output "$TMPDIR/clients-arklib"
  '';
  installPhase = ''
    mkdir -p "$out/share/zkc/lean" "$out/share/zkc/common/tests" "$out/reports"
    # Replace temporary absolute links before publishing the package.
    for dependency in integrations/arklib/.lake/packages/*; do
      if [ -L "$dependency" ]; then
        name=$(basename "$dependency")
        rm "$dependency"
        if [ -d "security/.lake/packages/$name" ]; then
          ln -s "../../../../security/.lake/packages/$name" "$dependency"
        else
          ln -s "../../../../.lake/packages/$name" "$dependency"
        fi
      fi
    done
    cp -a . "$out/share/zkc/lean/"
    # Logs and source records remain useful; temporary dependency links do not.
    (cd "$TMPDIR/clients-arklib" &&
      find . -type f ! -path '*/.lake/*' -exec cp --parents {} "$out/reports/" \;)
  '';
  dontFixup = true;
  meta = {
    description = "Pinned ArkLib integration and standalone consumer audits";
    license = lib.licenses.asl20;
    platforms = [ "x86_64-linux" ];
  };
}
