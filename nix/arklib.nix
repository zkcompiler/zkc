{
  lib,
  stdenvNoCC,
  formal,
  source,
  lean,
  git,
  python3,
  lakeSources,
}:
stdenvNoCC.mkDerivation {
  pname = "zkc-arklib";
  version = "0.1.0";
  dontUnpack = true;
  dontConfigure = true;
  nativeBuildInputs = [
    lean
    git
    python3
  ];
  buildPhase = ''
    cp -R ${formal.library}/share/zkc/formal formal
    mkdir -p tests
    cp -R ${formal.library}/share/zkc/tests/fixtures tests/fixtures
    chmod -R u+w formal
    cp -R ${source}/formal/integrations formal/
    chmod -R u+w formal/integrations
    cd formal
    mkdir -p integrations/arklib/.lake/packages
    for dependency in ${lakeSources}/*; do
      name=$(basename "$dependency")
      if [ -d ".lake/packages/$name" ]; then
        ln -s "$PWD/.lake/packages/$name" "integrations/arklib/.lake/packages/$name"
      else
        cp -R "$dependency/" "integrations/arklib/.lake/packages/$name"
        chmod -R u+w "integrations/arklib/.lake/packages/$name"
        git -C "integrations/arklib/.lake/packages/$name" reset --mixed HEAD
      fi
    done
    export LEAN_NUM_THREADS="$NIX_BUILD_CORES"
    export MATHLIB_NO_CACHE_ON_UPDATE=1
    (cd integrations/arklib && lake --no-cache build)
  '';
  doCheck = true;
  checkPhase = ''
    python3 checks/check_clients.py --with-arklib --output "$TMPDIR/clients-arklib"
  '';
  installPhase = ''
    mkdir -p "$out/share/zkc/formal" "$out/share/zkc/tests" "$out/reports"
    # Replace temporary absolute links before publishing the package.
    for dependency in integrations/arklib/.lake/packages/*; do
      if [ -L "$dependency" ]; then
        name=$(basename "$dependency")
        rm "$dependency"
        ln -s "../../../../.lake/packages/$name" "$dependency"
      fi
    done
    cp -a . "$out/share/zkc/formal/"
    cp -R ../tests/fixtures "$out/share/zkc/tests/fixtures"
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
