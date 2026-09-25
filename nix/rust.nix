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
  cargoHash = "sha256-VA4RiJLbvzZDmPCi5MPFJ5soRl3eLO5W2ieJbFpqQLw=";
  cargoBuildFlags = [
    "--workspace"
    "--bins"
    "--examples"
  ];
  # Cross-language tests run separately with the compiler and formal checkers.
  doCheck = false;
  postInstall = ''
    mkdir -p "$testSupport/bin/examples"
    for executable in "$out/bin/"*; do
      ln -s "$executable" "$testSupport/bin/"
    done
    # Cargo keeps a hashed copy beside each example; hyphens in public names
    # (such as vector-service) are significant and must remain installable.
    find target -regextype posix-extended -path '*/release/examples/*' \
      -type f -executable ! -regex '.*-[0-9a-f]{16}' \
      -exec cp {} "$testSupport/bin/examples/" \;
  '';
  meta = {
    description = "Protocol runtime and artifact host tools";
    license = lib.licenses.asl20;
    platforms = [ "x86_64-linux" ];
    mainProgram = "zkc";
  };
}
