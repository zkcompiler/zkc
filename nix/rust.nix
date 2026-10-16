{
  lib,
  rustPlatform,
  source,
}:
rustPlatform.buildRustPackage {
  pname = "zkc-tools";
  version = "0.0.0";
  src = source;
  cargoHash = "sha256-ka0tu89399pCO7hp5bgv/WrH7dvLP2lftaPFEuN9l1M=";
  cargoBuildFlags = [
    "-p"
    "zkc-tools"
    "--bin"
    "zkc"
  ];
  # Unit and integration checks have independent derivations. The product never
  # enables test providers through workspace feature unification.
  doCheck = false;
  meta = {
    description = "Program runtime and common Host tools";
    license = lib.licenses.asl20;
    platforms = [ "x86_64-linux" ];
    mainProgram = "zkc";
  };
}
