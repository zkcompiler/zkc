{
  stdenvNoCC,
  source,
  clang-tools,
  python3,
}:
stdenvNoCC.mkDerivation {
  name = "zkc-format-checks";
  src = source;
  nativeBuildInputs = [
    clang-tools
    python3
  ];
  dontConfigure = true;
  dontBuild = true;
  doCheck = true;
  checkPhase = "python3 scripts/format.py --tool=${clang-tools}/bin/clang-format-unwrapped";
  installPhase = ''mkdir -p "$out"'';
}
