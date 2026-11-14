{
  lib,
  stdenvNoCC,
  leanToolchain,
  git,
  python3,
  source,
  lakeSources,
  package,
  packageDirectory,
  dependencies ? [ ],
}:
stdenvNoCC.mkDerivation {
  pname = "zkc-${package}";
  version = "0.0.0";
  outputs = [
    "out"
    "library"
  ];
  dontUnpack = true;
  nativeBuildInputs = [
    leanToolchain
    git
    python3
  ];
  dontConfigure = true;
  buildPhase = ''
    runHook preBuild
    mkdir lean
    ${lib.concatMapStringsSep "\n" (dependency: ''
      cp -R ${dependency.library}/share/zkc/lean/. lean/
      chmod -R u+w lean
    '') dependencies}
    cp -R ${source}/lean/. lean/
    chmod -R u+w lean
    cd lean
    mkdir -p ${packageDirectory}/.lake/packages
    # A package without a Lake dependency has an empty source set.
    shopt -s nullglob
    for dependency in ${lakeSources}/*; do
      cp -R "$dependency/" "${packageDirectory}/.lake/packages/$(basename "$dependency")"
    done
    chmod -R u+w ${packageDirectory}/.lake/packages
    # Restore the index omitted by the canonical pinned source transport.
    for dependency in ${packageDirectory}/.lake/packages/*; do
      git -C "$dependency" reset --mixed HEAD
    done
    shopt -u nullglob
    python3 -c 'from pathlib import Path; from support.compatibility import prepare; prepare(Path("${packageDirectory}").resolve())'
    export LEAN_NUM_THREADS="$NIX_BUILD_CORES"
    export MATHLIB_NO_CACHE_ON_UPDATE=1
    (cd ${packageDirectory} && lake --no-cache build)
    runHook postBuild
  '';
  doCheck = true;
  checkPhase = ''
    runHook preCheck
    python3 checks/check_library.py --package ${package}
    python3 checks/check_package_ownership.py --package ${package}
    python3 checks/audit_imports.py --package ${package}
    ${lib.optionalString
      (builtins.elem package [
        "verification"
        "applications"
      ])
      ''
        python3 checks/check_clients.py --package ${package} --output "$TMPDIR/clients"
      ''
    }
    runHook postCheck
  '';
  installPhase = ''
    runHook preInstall
    mkdir -p "$library/share/zkc/lean" "$out/bin" "$out/reports"
    cp -a . "$library/share/zkc/lean/"
    for executable in "$library/share/zkc/lean/${packageDirectory}/.lake/build/bin/"*; do
      if [ -f "$executable" ] && [ -x "$executable" ]; then
        name=$(basename "$executable")
        mv "$executable" "$out/bin/$name"
        ln -s "$out/bin/$name" "$executable"
      fi
    done
    ${lib.optionalString
      (builtins.elem package [
        "verification"
        "applications"
      ])
      ''
        (cd "$TMPDIR/clients" &&
          find . -type f ! -path '*/.lake/*' -exec cp --parents {} "$out/reports/" \;)
      ''
    }
    runHook postInstall
  '';
  # Lake traces hash native artifacts. Preserve the bytes Lake built.
  dontFixup = true;
  meta = {
    description = "Independent ${package} Lean package and dependency closure audits";
    license = lib.licenses.asl20;
    platforms = [ "x86_64-linux" ];
  };
}
