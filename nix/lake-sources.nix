{
  lib,
  callPackage,
  linkFarm,
}:
manifestFile:
let
  manifest = builtins.fromJSON (builtins.readFile manifestFile);
  hashes = builtins.fromJSON (builtins.readFile ./lake-sources.json);
  fetchSource = callPackage ./git-source.nix { };
  packages = builtins.filter (package: package.type == "git") manifest.packages;
  source =
    package:
    let
      pin = hashes.${package.rev} or (throw "Prefetch the Lake source ${package.name} at ${package.rev}");
    in
    assert pin.url == package.url;
    fetchSource {
      inherit (package) url rev;
      inherit (pin) hash format;
    };
in
linkFarm "zkc-lake-sources" (
  map (package: {
    name = lib.removeSuffix "»" (lib.removePrefix "«" package.name);
    path = source package;
  }) packages
)
