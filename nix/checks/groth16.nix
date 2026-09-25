{
  tools,
  compiler,
  formal,
  groth16,
  nodejs,
  python3,
  environment,
}:
tools.overrideAttrs (
  old:
  (environment.outputs {
    compilerBin = "${compiler}/bin";
    nativeBin = "${tools.testSupport}/bin";
    leanBin = "${formal}/bin";
  })
  // {
    CARGO_NET_OFFLINE = "true";
    pname = "zkc-groth16-checks";
    cargoBuildFlags = old.cargoBuildFlags ++ [ "--all-features" ];
    nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [
      nodejs
      python3
    ];
    doCheck = true;
    checkPhase = ''
      runHook preCheck
      ${environment.checks}
      cp -R ${groth16} "$TMPDIR/fixture"
      chmod -R u+w "$TMPDIR/fixture"
      python3 tests/run.py groth16 --fixture "$TMPDIR/fixture"
      zkc_bin=$(find target -path '*/release/groth16-artifact' -type f -print -quit)
      test -n "$zkc_bin"
      python3 tests/groth16/run_zkc.py --workdir "$TMPDIR/fixture" \
        --zkc "$PWD/$zkc_bin" --compiler "$ZKC_COMPILER_BIN/zkc-compile" --lean "$ZKC_LEAN_BIN/interactive-protocol" \
        --source examples/protocols/groth16.pir
      runHook postCheck
    '';
    postInstall = (old.postInstall or "") + ''
      mkdir -p "$out/reports"
      cp "$TMPDIR/fixture/RESULTS.json" "$out/reports/fixtures.json"
      cp "$TMPDIR/fixture/zkc/RESULTS.json" "$out/reports/interoperability.json"
    '';
  }
)
