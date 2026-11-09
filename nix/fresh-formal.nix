# Force source reconstruction throughout the actual Lake dependency graph.
{
  packages,
  runId,
  lib,
}:
assert runId != "";
let
  inventory = import ./lean-packages.nix { inherit lib; };
  fresh = lib.mapAttrs (
    name: entry:
    (packages.${name}.override {
      dependencies = map (dependency: fresh.${dependency}) entry.dependencies;
    }).overrideAttrs
      { ZKC_CI_FRESH_RUN = runId; }
  ) inventory;
in
fresh
