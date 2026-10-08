# Optional independent research checks; never a dependency of native execution.
{
  stdenvNoCC,
  source,
  formal,
  lean,
  environment,
  python3,
  git,
}:
stdenvNoCC.mkDerivation {
  pname = "zkc-formal-checks";
  version = "0.1.0";
  src = source;
  nativeBuildInputs = [
    lean
    python3
    git
  ];
  dontConfigure = true;
  dontBuild = true;
  doCheck = true;
  checkPhase = ''
    runHook preCheck
    ${environment.checks}
    export LEAN_NUM_THREADS="$zkc_check_cores"
    cp -R ${formal.library}/share/zkc/formal/.lake formal/
    chmod -R u+w formal/.lake
    python3 tests/run.py lean
    runHook postCheck
  '';
  installPhase = ''
    mkdir -p "$out"
    find build/reports -type f ! -path '*/.lake/*' -exec cp --parents {} "$out/" \;
    mv "$out/build/reports" "$out/reports"
    rmdir "$out/build"
  '';
}
