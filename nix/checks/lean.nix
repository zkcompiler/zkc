# Optional independent research checks; never a dependency of native execution.
{
  stdenvNoCC,
  source,
  lean,
  core,
  leanToolchain,
  environment,
  python3,
  git,
}:
stdenvNoCC.mkDerivation {
  pname = "zkc-lean-checks";
  version = "0.0.0";
  src = source;
  nativeBuildInputs = [
    leanToolchain
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
    cp -R ${lean.library}/share/zkc/lean/. lean/
    chmod -R u+w lean
    # Nothing that Applications requires reaches Core, so its tree does not contain it.
    cp -R ${core.library}/share/zkc/lean/core lean/
    chmod -R u+w lean
    python3 common/tests/run.py lean
    runHook postCheck
  '';
  installPhase = ''
    mkdir -p "$out"
    find build/reports -type f ! -path '*/.lake/*' -exec cp --parents {} "$out/" \;
    mv "$out/build/reports" "$out/reports"
    rmdir "$out/build"
  '';
}
