{
  lib,
  rustPlatform,
  source,
}:
rustPlatform.buildRustPackage {
  pname = "zkc-tools";
  version = "0.1.0";
  src = source;
  outputs = [
    "out"
    "testSupport"
  ];
  cargoHash = "sha256-F32XtlYqUGXij/UQBMLSMEBK0UuuFYcGUCi77QfkKoQ=";
  cargoBuildFlags = [
    "--workspace"
    "--bins"
    "--examples"
    "--all-features"
  ];
  # Native integration tests run separately with the compiler.
  doCheck = false;
  postInstall = ''
    mkdir -p "$testSupport/bin/examples"
    for executable in "$out/bin/"*; do
      ln -s "$executable" "$testSupport/bin/"
    done
    # Cargo keeps a hashed copy beside each example; install only public names.
    find target -regextype posix-extended -path '*/release/examples/*' \
      -type f -executable ! -regex '.*-[0-9a-f]{16}' \
      -exec cp {} "$testSupport/bin/examples/" \;
  '';
  meta = {
    description = "Program runtime and common Host tools";
    license = lib.licenses.asl20;
    platforms = [ "x86_64-linux" ];
    mainProgram = "zkc";
  };
}
